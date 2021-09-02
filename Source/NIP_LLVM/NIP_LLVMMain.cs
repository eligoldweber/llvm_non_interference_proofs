using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Reflection;
namespace NIP.LLVM
{
    public class IllegalDafnyFile : Exception { }
    
    public class DafnyFile {
    public string FilePath { get; private set; }
    public string BaseName { get; private set; }
    public bool isPrecompiled { get; private set; }
    public string SourceFileName { get; private set; }

    public static List<string> fileNames(IList<DafnyFile> dafnyFiles) {
      var sourceFiles = new List<string>();
      foreach (DafnyFile f in dafnyFiles) {
        sourceFiles.Add(f.FilePath);
      }
      return sourceFiles;
    }

    // public DafnyFile(string filePath) {
    //   FilePath = filePath;
    //   BaseName = Path.GetFileName(filePath);

    //   var extension = Path.GetExtension(filePath);
    //   if (extension != null) { extension = extension.ToLower(); }

    //   if (extension == ".dfy" || extension == ".dfyi" || extension == ".cdfy" || extension == ".arm") {
    //     isPrecompiled = false;
    //     SourceFileName = filePath;
    //   } else if (extension == ".dll") {
    //     isPrecompiled = true;
    //     Assembly.ReflectionOnlyLoad("DafnyRuntime");
    //     var asm = Assembly.ReflectionOnlyLoadFrom(filePath);
    //     string sourceText = null;
    //     foreach (var adata in asm.GetCustomAttributesData()) {
    //       if (adata.Constructor.DeclaringType.Name == "DafnySourceAttribute") {
    //         foreach (var args in adata.ConstructorArguments) {
    //           if (args.ArgumentType == System.Type.GetType("System.String")) {
    //             sourceText = (string)args.Value;
    //           }
    //         }
    //       }
    //     }

    //     if (sourceText == null) { throw new IllegalDafnyFile(); }
    //     SourceFileName = Path.GetTempFileName();
    //     File.WriteAllText(SourceFileName, sourceText);

    //   } else {
    //     throw new IllegalDafnyFile();
    //   }


    // }
  }
}