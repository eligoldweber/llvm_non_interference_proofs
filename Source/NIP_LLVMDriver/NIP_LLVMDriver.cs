using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;


namespace NIP.LLVM
{
    
  public class DafnyDriver
    {

      public static int Main(string[] args)
      {
        Console.WriteLine("Starting NIP_LLVM");
        DafnyFile d = new DafnyFile("../../Dafny/memory.dfy");
        Console.WriteLine("memory is valid Dafny File : " + d.SourceFileName);
        int ret = 0;
        return ret;
      }

    }

}
