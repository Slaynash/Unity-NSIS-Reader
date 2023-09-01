using System;
using System.Collections.Generic;
using System.IO;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.RegularExpressions;

namespace UnityNSISReader
{
    class Program
    {
        private const uint FhFlagsMask = 255;
        private const uint FhSig = 0xDEADBEEF;
        private const uint FhInt1 = 0x6C6C754E, FhInt2 = 0x74666F73, FhInt3 = 0x74736E49;

        private static byte[] Utf8Limits = new[] { (byte)0xC0, (byte)0xE0, (byte)0xF0, (byte)0xF8, (byte)0xFC };

        private const uint SignatureSize = 16;
        private const uint StartHeaderSize = 28;

        private const uint MaskIsCompressed = unchecked((uint)(1 << 31));

        private const uint PageSize = 16 * 4;
        private const uint NumCommandParams = 6;
        private const uint CommandSize = 4 + NumCommandParams * 4;


        private static string sourceFile;
        private static string outDir;
        private static string filter;


        private static long m_length;
        private static int m_pos;
        private static int g_filehdrsize;

        private static bool IsUnicode;
        private static uint NumStringChars;

        private static unsafe Header* g_header;
        private static unsafe byte* pData;
        private static unsafe BlockHeader* bhPages;
        private static unsafe BlockHeader* bhSections;
        private static unsafe BlockHeader* bhEntries;
        private static unsafe BlockHeader* bhStrings;
        private static unsafe BlockHeader* bhLangTables;
        private static unsafe BlockHeader* bhCtlColors;
        private static unsafe BlockHeader* bhFonts;
        private static unsafe BlockHeader* bhDatas;

        private static readonly string[] VarStrings = new[]
        {
            "CMDLINE",
            "INSTDIR",
            "OUTDIR",
            "EXEDIR",
            "LANGUAGE",
            "TEMP",
            "PLUGINSDIR",
            "EXEPATH",   // NSIS 2.26+
            "EXEFILE",   // NSIS 2.26+
            "HWNDPARENT",
            "_CLICK",    // is set from page->clicknext
            "_OUTDIR"    // NSIS 2.04+
        };

        private static readonly int NumInternalVars = 20 + VarStrings.Length;

        private static readonly string[] PageTypes = new[]
        {
            "license",
            "components",
            "directory",
            "instfiles",
            "uninstConfirm",
            "COMPLETED",
            "custom"
        };


        static unsafe int Main(string[] args)
        {
            foreach (string arg in args)
            {
                if (arg.StartsWith("-f"))
                {
                    sourceFile = arg.Substring(2);
                    if (!File.Exists(sourceFile))
                        throw new FileNotFoundException("Failed to find the file " + sourceFile);
                }
                else if (arg.StartsWith("-o"))
                {
                    outDir = arg.Substring(2);
                    Directory.CreateDirectory(outDir);
                }
                else if (arg.StartsWith("-r"))
                {
                    filter = arg.Substring(2);
                }
            }

            if (string.IsNullOrEmpty(sourceFile) || string.IsNullOrEmpty(outDir))
            {
                Console.WriteLine("Usage: UnityNSISReader.exe -f<FileName> -o<OutputPath> [-r<regex>]\n\tr: Filter the results using a regex");
                return -1;
            }

            Console.WriteLine("filter: " + filter);

            //byte[] fba = File.ReadAllBytes(sourceFile);
            FileStream fs = new FileStream(sourceFile, FileMode.Open);
            //fixed (byte* f = fba)
            {
                FirstHeader h = default;

                Console.WriteLine("Checking header");

                long left = m_length = fs.Length;
                int l = (int)Math.Min(left, g_filehdrsize != 0 ? 32768 : 512);
                byte[] temp = new byte[l];
                while (left > 0)
                {
                    l = (int)Math.Min(left, g_filehdrsize != 0 ? 32768 : 512);
                    fs.Read(temp, 0, l);
                    //byte* temp = f + m_pos;

                    if (g_filehdrsize == 0)
                    {
                        //h = (FirstHeader*)temp;
                        fixed (byte* p = temp)
                            h = Marshal.PtrToStructure<FirstHeader>((IntPtr)p);

                        if (
                            (h.flags & ~FhFlagsMask) == 0 &&
                            h.siginfo == FhSig &&
                            h.nsinst2 == FhInt3 &&
                            h.nsinst1 == FhInt2 &&
                            h.nsinst0 == FhInt1
                        )
                        {
                            g_filehdrsize = m_pos;
                            Console.WriteLine($"Found nsis data at {g_filehdrsize:X}");
                            break;
                        }
                    }

                    m_pos += l;
                    left -= l;
                }

                if (g_filehdrsize == 0)
                {
                    Console.Error.WriteLine("Failed to locate NSIS data in the target file");
                    return -1;
                }

                // INVALID ENDIAN
                Console.WriteLine("Installer: " + ((h.flags & (uint)NFlags.kUninstall) == 0));
                bool isNSISBI = (h.flags & 0x30) != 0;
                Console.WriteLine("NSISBI: " + isNSISBI);
                //uint headerSize = *(uint*)((byte*)h + SignatureSize + 4);
                //uint arcSize = *(uint*)((byte*)h + SignatureSize + 8);
                uint headerSize = BitConverter.ToUInt32(temp, (int)SignatureSize + 4);
                uint arcSize = BitConverter.ToUInt32(temp, (int)SignatureSize + 8);
                Console.WriteLine("Header Size: " + headerSize);
                Console.WriteLine("Arc Size: " + arcSize);
                if (arcSize <= StartHeaderSize)
                {
                    Console.Error.WriteLine("Arc size is less than StartHeaderSize. This should not happen !");
                    return -1;
                }


                bool headerIsCompressed = true;
                uint dictionarySize = 1;
                bool isSolid = true;
                uint nonSolidStartOffset = 0;

                byte[] sig = new byte[8 + 11];
                int sigOffset = 0;
                //byte* sig = (byte*)h + SignatureSize + 8 + 4;
                Array.Copy(temp, (int)SignatureSize + 8 + 4, sig, 0, 19);
                if (isNSISBI)
                    sigOffset += 8;
                uint compressedHeaderSize = BitConverter.ToUInt32(sig, sigOffset);
                Console.WriteLine("Compressed Header Size: " + compressedHeaderSize.ToString("X4"));

                if (compressedHeaderSize == headerSize)
                {
                    isSolid = false;
                    headerIsCompressed = false;
                    Console.WriteLine("Header is NOT compressed");
                }
                else if (IsLZMA(sig, sigOffset, ref dictionarySize))
                {
                    Console.WriteLine("Header is LZMA compressed (Solid)");
                }
                else if (sig[sigOffset + 3] == 0x80)
                {
                    isSolid = false;
                    if (IsLZMA(sig, sigOffset + 4, ref dictionarySize) && sig[sigOffset + 3] == 0x80)
                        Console.WriteLine("Header is LZMA compressed (Non-Solid)");
                    else if (IsBZip2(sig, sigOffset + 4))
                        Console.WriteLine("Header is BZip2 compressed (Non-Solid)");
                    else
                        Console.WriteLine("Header is Deflate compressed (Non-Solid)");
                }
                else if (IsBZip2(sig, sigOffset))
                    Console.WriteLine("Header is BZip2 compressed (Solid)");
                else
                {
                    Console.WriteLine("Header is Deflate compressed (Solid)");
                    sigOffset -= 4;
                }

                if (!isSolid)
                {
                    headerIsCompressed = ((compressedHeaderSize & MaskIsCompressed) != 0);
                    compressedHeaderSize &= ~MaskIsCompressed;
                    nonSolidStartOffset = compressedHeaderSize;
                }

                byte[] _data;// = new byte[headerSize];
                //byte[] buffer = new byte[arcSize]; // -44 ?
                //Marshal.Copy((IntPtr)(sig + 4), buffer, 0, (int)arcSize);
                long sigFilePos = g_filehdrsize + (int)SignatureSize + 8 + 4 + sigOffset;
                fs.Position = sigFilePos + 4;


                //using (DeflateStream ds = new DeflateStream(new MemoryStream(buffer), CompressionMode.Decompress))
                /*
                using (GZipStream ds = new GZipStream(new MemoryStream(buffer), CompressionMode.Decompress))
                {
                    if (isSolid)
                    {
                        byte[] buf = new byte[4];
                        ds.Read(buf, 0, 4);
                        uint bufValue = BitConverter.ToUInt32(buf, 0);
                        if (bufValue != headerSize)
                        {
                            Console.Error.WriteLine("Solid size mismatch header size (" + bufValue + " vs " + headerSize + ")");
                            return;
                        }
                        Console.Error.WriteLine("bufValue is valid");
                    }
                    ds.Read(_data, 0, (int)headerSize);
                }
                */

                SevenZip.Compression.LZMA.Decoder lzmadecoder = new SevenZip.Compression.LZMA.Decoder();
                byte[] properties = new byte[5];
                //Array.Copy(buffer, properties, 5);
                fs.Read(properties, 0, 5);
                lzmadecoder.SetDecoderProperties(properties);
                //long fileLength = BitConverter.ToInt64(buffer, 5);
                //Console.WriteLine("[LZMA] fileLength: " + fileLength);
                MemoryStream outputStream = new MemoryStream(1 << 20);
                lzmadecoder.Code(fs, outputStream, arcSize - 5, 1 << 20, null);
                if (isSolid)
                {
                    byte[] buf = new byte[4];
                    outputStream.Read(buf, 0, 4);
                    uint bufValue = BitConverter.ToUInt32(buf, 0);
                    if (bufValue != headerSize)
                    {
                        Console.Error.WriteLine("Solid size mismatch header size (" + bufValue + " vs " + headerSize + ")");
                        return -1;
                    }
                    Console.Error.WriteLine("bufValue is valid");
                    _data = new byte[headerSize - 4];

                    int sbr = 0;
                    do
                    {
                        int sr = outputStream.Read(_data, 0, (int)headerSize - 4);
                        if (sr <= 0)
                            throw new Exception("Failed to read header (" + sr + ")");
                        sbr += sr;
                    }
                    while (sbr < headerSize - 4);
                }
                else
                    _data = outputStream.ToArray();

                fixed (byte* p = _data)
                {
                    pData = p;
                    bhPages = (BlockHeader*)(p + 4 + 8 * 0);
                    bhSections = (BlockHeader*)(p + 4 + 8 * 1);
                    bhEntries = (BlockHeader*)(p + 4 + 8 * 2);
                    bhStrings = (BlockHeader*)(p + 4 + 8 * 3);
                    bhLangTables = (BlockHeader*)(p + 4 + 8 * 4);
                    bhCtlColors = (BlockHeader*)(p + 4 + 8 * 5);
                    bhFonts = (BlockHeader*)(p + 4 + 8 * 6);
                    bhDatas = (BlockHeader*)(p + 4 + 8 * 7);

                    Console.WriteLine("Entries: " + bhEntries->num + " starting at " + bhEntries->offset + " (Valid: " + (bhEntries->offset < headerSize) + ")");
                    Console.WriteLine("Strings: " + bhStrings->num + " starting at " + bhStrings->offset + " (Valid: " + (bhStrings->offset < headerSize) + ")");
                    Console.WriteLine("LangTables: " + bhLangTables->num + " starting at " + bhLangTables->offset + " (Valid: " + (bhLangTables->offset < headerSize) + ")");

                    if (
                        bhEntries->offset > headerSize ||
                        bhStrings->offset > headerSize ||
                        bhLangTables->offset > headerSize
                    )
                    {
                        Console.Error.WriteLine("BlockHeader offsets are out of bounds!");
                        return -1;
                    }

                    if (bhLangTables->offset < bhStrings->offset)
                    {
                        Console.Error.WriteLine("bhLangTables is before bhStrings");
                        return -1;
                    }
                    uint stringTableSize = bhLangTables->offset - bhStrings->offset;
                    Console.WriteLine("stringTableSize: " + stringTableSize);
                    if (stringTableSize < 2)
                    {
                        Console.Error.WriteLine("stringTableSize is less than 2 (" + stringTableSize + ")");
                        return -1;
                    }
                    byte* strData = p + bhStrings->offset;
                    if (strData[stringTableSize - 1] != 0)
                    {
                        Console.Error.WriteLine("byte at stringTableSize-1 is not 0");
                        return -1;
                    }
                    Console.WriteLine("byte at stringTableSize-1 is 0");
                    IsUnicode = *(short*)strData == 0;
                    Console.WriteLine("Unicode: " + IsUnicode + " (" + *(short*)strData + ")");
                    NumStringChars = stringTableSize;
                    if (IsUnicode)
                    {
                        if ((stringTableSize & 1) != 0)
                        {
                            Console.Error.WriteLine("(stringTableSize & 1) is not 0");
                            return -1;
                        }
                        NumStringChars >>= 1;
                        if ((strData[stringTableSize - 2]) != 0)
                        {
                            Console.Error.WriteLine("(strData[stringTableSize - 2]) is not 0");
                            return -1;
                        }
                    }
                    Console.WriteLine("NumStringChars: " + NumStringChars);

                    if (bhEntries->num > (1 << 25))
                    {
                        Console.Error.WriteLine("bhEntries is too big (1)");
                        return -1;
                    }
                    if (bhEntries->num * 28 > headerSize - bhEntries->offset)
                    {
                        Console.Error.WriteLine("bhEntries is too big (2)");
                        return -1;
                    }


                    Console.WriteLine("Done checking header");
                    Console.WriteLine();

                    byte* cmdPtr = null;

                    Console.WriteLine();

                    // Commands
                    cmdPtr = p + bhEntries->offset;

                    uint commandSize = CommandSize;
                    if (isNSISBI)
                        commandSize += 2 * 4;

                    string currentOutPath = "";

                    // TODO list label offsets

                    List<string> files = new List<string>();

                    for (int kkk = 0; kkk < bhEntries->num; kkk++, cmdPtr += commandSize)
                    {
                        // TODO reset var values if new label

                        uint commandId = *(uint*)cmdPtr;

                        uint[] _params = new uint[NumCommandParams];

                        for (int i = 0; i < NumCommandParams; ++i)
                            _params[i] = *(uint*)(cmdPtr + 4 + 4 * i);

                        switch (commandId)
                        {
                            case 11:
                                bool isSetOutPath = (_params[1] != 0);
                                /*
                                string s = "";
                                if (isSetOutPath)
                                {
                                    uint par0 = _params[0];

                                    uint resOffset = 0;
                                    int idx = GetVarIndex(par0, ref resOffset);
                                    if (idx == 31 || idx == 22)
                                        par0 += resOffset;

                                    s += ReadString2_Raw(par0);
                                }
                                */

                                //Console.Write(isSetOutPath ? "SetOutPath" : "CreateDirectory");
                                //string path = ReadString2(_params[0]);
                                //if (isSetOutPath)
                                //    currentOutPath = path;
                                //Console.Write(" " + path);
                                //if (_params[2] != 0)
                                //    Console.Write(" ; CreateRestrictedDirectory");

                                string outPath = ReadString2(_params[0]).Replace("$OUTDIR", "").Replace("$INSTDIR", "");
                                if (outPath == "$INSTDIR")
                                    outPath = "";

                                //Console.WriteLine(" --- > " + outPath);
                                if (outPath.EndsWith("/"))
                                    outPath = outPath.Substring(0, outPath.Length - 1);
                                currentOutPath = outPath;
                                /*
                                if (!Directory.Exists(currentOutPath))
                                    Directory.CreateDirectory(currentOutPath);
                                */
                                continue;

                            case 20:
                                //Console.Write("File");
                                string fileName = ReadString2(_params[1]);
                                //Console.Write(" " + fileName);
                                uint offset = _params[2];
                                //Console.Write(" @ " + offset);


                                if (isSolid)
                                    throw new NotImplementedException("Cannot decompress file in a Solid compression type");

                                //byte* fileData = sig + nonSolidStartOffset + 4 + _params[2];
                                fs.Position = sigFilePos + nonSolidStartOffset + 4 + _params[2];
                                byte[] sizeData = new byte[4];
                                fs.Read(sizeData, 0, 4);
                                //uint size = *(uint*)(fileData);
                                uint size = BitConverter.ToUInt32(sizeData, 0);
                                bool isFileCompressed = false;
                                if ((size & MaskIsCompressed) != 0)
                                {
                                    isFileCompressed = true;
                                    size &= ~MaskIsCompressed;
                                }
                                //Console.Write($" (size: {size} [compressed: {isFileCompressed}])");

                                string filePathLocal = Path.Combine(currentOutPath, fileName).Replace('\\', '/');
                                if (files.Contains(filePathLocal))
                                    continue;
                                files.Add(filePathLocal);

                                if (!string.IsNullOrEmpty(filter) && !Regex.IsMatch(filePathLocal, filter))
                                    continue;

                                Console.WriteLine(filePathLocal);

                                string filePath = Path.Combine(outDir, filePathLocal);
                                string filePathParent = Directory.GetParent(filePath).FullName;

                                //Console.Write($" (filePathReal: {filePathReal})");
                                Directory.CreateDirectory(filePathParent);
                                if (File.Exists(filePath))
                                    File.Delete(filePath);

                                //Console.WriteLine();


                                byte[] data = new byte[size];
                                Array.Copy(sizeData, data, 4);
                                int br = 0;
                                do
                                {
                                    int r = fs.Read(data, br + 4, (int)size - br - 4);
                                    if (r <= 0)
                                        throw new IOException("Failed to read data (" + r + ")");
                                    br += r;
                                }
                                while (br < size - 4);

                                if (isFileCompressed)
                                {
                                    //Marshal.Copy((IntPtr)fileData, data, 0, (int)size);

                                    SevenZip.Compression.LZMA.Decoder lzmadecoder2 = new SevenZip.Compression.LZMA.Decoder();
                                    byte[] properties2 = new byte[5];
                                    Array.Copy(data, 4, properties, 0, 5);
                                    lzmadecoder2.SetDecoderProperties(properties);
                                    //long fileLength2 = BitConverter.ToInt64(data, 4 + 5);
                                    //Console.WriteLine("[LZMA] fileLength: " + fileLength2);
                                    MemoryStream outputStream2 = new MemoryStream(1 << 28);
                                    lzmadecoder2.Code(new MemoryStream(data, 4 + 5, (int)size - (4 + 5)), outputStream2, data.Length - (4 + 5), 1 << 28, null);

                                    /*
                                    SevenZip.Compression.LZMA.Decoder lzmadecoder2 = new SevenZip.Compression.LZMA.Decoder();
                                    byte[] properties2 = new byte[5];
                                    Array.Copy(data, 4, properties, 0, 5);
                                    lzmadecoder2.SetDecoderProperties(properties);
                                    //long fileLength2 = BitConverter.ToInt64(data, 4 + 5);
                                    //Console.WriteLine("[LZMA] fileLength: " + fileLength2);
                                    MemoryStream outputStream2 = new MemoryStream(1 << 28);
                                    lzmadecoder2.Code(new MemoryStream(data, 4 + 5, data.Length - (4 + 5)), outputStream2, data.Length - (4 + 5), 1 << 28, null);
                                    */
                                    if (isSolid)
                                    {
                                        /*
                                        byte[] buf = new byte[4];
                                        outputStream.Read(buf, 0, 4);
                                        uint bufValue = BitConverter.ToUInt32(buf, 0);
                                        if (bufValue != headerSize)
                                        {
                                            Console.Error.WriteLine("Solid size mismatch header size (" + bufValue + " vs " + headerSize + ")");
                                            return;
                                        }
                                        Console.Error.WriteLine("bufValue is valid");
                                        */
                                        _data = new byte[outputStream2.Length];
                                        outputStream.Read(_data, 4, (int)outputStream2.Length);
                                    }
                                    else
                                        _data = outputStream2.ToArray();
                                }
                                else
                                {
                                    //Marshal.Copy((IntPtr)(fileData + 4), data, 0, (int)size);

                                    _data = data;
                                }



                                File.WriteAllBytes(filePath, _data);

                                continue;
                        }

                        /*
                        Console.Write(commandId);

                        for (int i = 0; i < NumCommandParams; ++i)
                        {
                            Console.Write(" ");
                            Console.Write(ReadString2(_params[i]));
                        }

                        Console.Write("    ;");

                        for (int i = 0; i < NumCommandParams; ++i)
                        {
                            Console.Write(" " + (int)_params[i]);
                        }

                        Console.WriteLine();
                        */
                        /*
                        switch (commandId)
                        {
                            case NsisCommands.CreateDir:

                                break;
                        }
                        */
                    }
                }

                /*

                uint inputLen = *(uint*)(f + g_filehdrsize + sizeof(FirstHeader));

                Console.WriteLine("Input Length is " + inputLen + ". Compressed: " + ((inputLen & 0x80000000) > 0));

                byte* data = f + g_filehdrsize + sizeof(FirstHeader) + sizeof(int);

                Header* header = g_header = (Header*)data;

                header->blockSections.offset += (int)data;
                header->blockEntries.offset += (int)data;
                header->blockStrings.offset += (int)data;
                header->blockLangTables.offset += (int)data;
                header->blockCtlColors.offset += (int)data;
                header->blockData.offset += (int)data;


                Console.WriteLine("installRegKeyPtr: " + header->installRegKeyPtr);
                Console.WriteLine("Str: " + GetNSISString(header->installDirectoryPtr));
                */
            }


            Console.WriteLine();

            return 0;
        }

        private static unsafe string ReadString2(uint pos)
        {
            if (pos < 0)
                return $"$(LSTR_{-(pos + 1)})";
            else if (pos >= NumStringChars)
                return "$_ERROR_STR_" + pos;
            else
            {
                if (IsUnicode)
                    return GetNsisStringUnicode(pData + bhStrings->offset + pos * 2);
                else
                    return GetNsisString(pData + bhStrings->offset + pos);
            }
        }

        private static string ReadString2_Raw(uint pos)
        {
            if (pos < 0)
                return $"$(LSTR_{-(pos + 1)})";
            else if (pos >= NumStringChars)
                return "$_ERROR_STR_" + pos;
            else
            {
                return $"S_{pos}";
            }
        }

        private static unsafe string GetNsisStringUnicode(byte* p)
        {
            StringBuilder sb = new StringBuilder();
            for (; ; )
            {
                ushort c = *(ushort*)p;
                p += 2;
                //Console.Write($"[C{c:X4}]");
                if (c == 0)
                    break;
                if (false /*IsPark()*/)
                {
                    if (c >= 0xE000 && c <= 0xE003)
                    {
                        ushort n = *(ushort*)p;
                        p += 2;
                        if (n == 0)
                            break;
                        if (c != 0xE000)
                        {
                            if (c == 0xE002)
                                sb.Append($"$(SSTR_{n & 0xFF}_{n >> 8})");
                            else
                            {
                                n &= 0x7FFF;
                                if (c == 0xE001)
                                    sb.Append(GetVar(n));
                                else
                                    sb.Append($"$(LSTR_{n})");
                            }
                            continue;
                        }
                        c = n;
                    }
                }
                else
                {
                    if (c <= 4)
                    {
                        ushort n = *(ushort*)p;
                        //Console.Write($"[N{n:X4}]");
                        p += 2;
                        if (n == 0)
                            break;
                        if (c != 4)
                        {
                            if (c == 2)
                                sb.Append($"$(SSTR_{n & 0xFF}_{n >> 8})");
                            else
                            {
                                n = (ushort)((n & 0x7F) | (((ushort)(n >> 8) & 0x7F) << 7));
                                if (c == 3)
                                    sb.Append(GetVar(n));
                                else
                                    sb.Append($"$(LSTR_{n})");
                            }
                            continue;
                        }
                        c = n;
                    }
                }

                if (c < 0x80)
                {
                    if (c == 9) sb.Append("$\\t");
                    else if (c == 10) sb.Append("$\\n");
                    else if (c == 13) sb.Append("$\\r");
                    else if (c == '"') sb.Append("$\\\"");
                    else if (c == '$') sb.Append("$$");
                    else sb.Append((char)c, 1);
                    //Console.Write($"[A:{(char)c}]");

                    continue;
                }

                short numAdds;
                for (numAdds = 1; numAdds < 5; ++numAdds)
                    if (c < (1 << (numAdds * 5 + 6)))
                    {
                        //Console.Write($"[NAB]");
                        break;
                    }

                sb.Append((char)(Utf8Limits[numAdds - 1] + (c >> (6 * numAdds))));
                do
                {
                    numAdds--;
                    sb.Append((char)(0x80 + ((c >> (6 * numAdds)) & 0x3F)));
                }
                while (numAdds != 0);
            }
            return sb.ToString();
        }

        private static unsafe string GetNsisString(byte* s)
        {
            string tmp = "";
            for (; ; )
            {
                byte c = *s++;
                if (c == 0)
                    return tmp;
                if (c <= 4)
                {
                    byte c0 = *s++;
                    if (c0 == 0)
                        return tmp;
                    if (c != 4)
                    {
                        byte c1 = *s++;
                        if (c1 == 0)
                            return tmp;
                        if (c1 == 4)
                            tmp += $"$(SSTR_{c0}_{c1})";
                        else
                        {
                            uint n = (uint)((ushort)(c0 & 0x7F) | ((ushort)(c1 & 0x7F) << 7));
                            if (c == 3)
                                tmp += GetVar(n);
                            else
                                tmp += $"$(LSTR_{n})";
                        }
                        continue;
                    }
                }
            }
        }

        private static string GetVar(uint index)
        {
            return "$" + GetVar2(index);
        }

        private static string GetVar2(uint index)
        {
            string tmp = "";
            if (index < 20)
            {
                if (index >= 10)
                {
                    tmp += "R";
                    index -= 10;
                }
                tmp += index;
            }
            else
            {
                if (index < NumInternalVars)
                {
                    tmp += VarStrings[index - 20];
                }
                else
                {
                    tmp += $"_{index - NumInternalVars}_";
                }
            }
            return tmp;
        }

        private static int GetVarIndex(uint strPos, ref uint resOffset)
        {
            resOffset = 0;
            int varIndex = GetVarIndex(strPos);
            if (varIndex < 0)
                return varIndex;
            if (IsUnicode)
            {
                if (NumStringChars - strPos < 2 * 2)
                    return -1;
                resOffset = 2;
            }
            else
            {
                if (NumStringChars - strPos < 3)
                    return -1;
                resOffset = 3;
            }
            return varIndex;
        }

        private static int GetVarIndex(uint strPos)
        {
            /*
            if (strPos >= NumStringChars)
                return -1;

            if (IsUnicode)
            {
                if (NumStringChars - strPos < 3 * 2)
                    return -1;

                byte* p = _data
            }
            */
            return -2;
        }

        private static unsafe bool IsLZMA_(byte[] p, int pOffset, ref uint dictionary)
        {
            dictionary = BitConverter.ToUInt32(p, pOffset + 1);
            return p[pOffset + 0] == 0x5D &&
                   p[pOffset + 1] == 0x00 && p[pOffset + 2] == 0x00 &&
                   p[pOffset + 5] == 0x00 && (p[pOffset + 6] & 0x80) == 0x00;
        }

        private static unsafe bool IsBZip2(byte[] p, int pOffset)
        {
            return (p[pOffset + 0] == 0x31 && p[pOffset + 1] < 14);
        }

        private static unsafe bool IsLZMA(byte[] p, int pOffset, ref uint dictionary)
        {
            if (IsLZMA_(p, pOffset, ref dictionary))
                return true;

            if (BitConverter.ToUInt32(p, pOffset) <= 1 && IsLZMA_(p, pOffset + 1, ref dictionary))
                return true;

            return false;
        }

        private static unsafe string GetNSISString(int strtab)
        {
            char* data = (char*)(g_header->blockStrings.offset + strtab);
            return new string(data);
        }

        public static int SwapEndianness(int value)
        {
            var b1 = (value >> 0) & 0xff;
            var b2 = (value >> 8) & 0xff;
            var b3 = (value >> 16) & 0xff;
            var b4 = (value >> 24) & 0xff;

            return b1 << 24 | b2 << 16 | b3 << 8 | b4 << 0;
        }
    }

    [StructLayout(LayoutKind.Sequential)]
    struct FirstHeader
    {
        public uint flags;
        public uint siginfo;

        public int nsinst0, nsinst1, nsinst2;

        public int length_of_header;
        public int length_of_all_following_data;
    }

    enum NFlags : uint
    {
        kUninstall = 1,
        kSilent = 2,
        kNoCrc = 4,
        kForceCrc = 8,
    }

    [StructLayout(LayoutKind.Sequential)]
    struct Header
    {
        public uint flags;
        public BlockHeader blockSections;
        public BlockHeader blockEntries;
        public BlockHeader blockStrings;
        public BlockHeader blockLangTables;
        public BlockHeader blockCtlColors;
        public BlockHeader blockData;

        public int installRegRootkey;
        public int installRegKeyPtr, installRegValuePtr;
    }

    struct BlockHeader
    {
        public uint offset;
        public uint num;
    }
}
