/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.wasm

import Definitions.FunDef

class FileWriter(module: Module) {

  import java.io.{File, FileWriter}

  def writeWasmText(): Unit = {
    val fw = new FileWriter(new File(module.name))
    fw.write(Printer(module))
    fw.flush()
  }

  def writeNodejsWrapper(fileName: String, moduleFile: String, toRun: Set[FunDef]): Unit = {
    val wrapperString =
      s"""|// `Wasm` does **not** understand node buffers, but thankfully a node buffer
          |// is easy to convert to a native Uint8Array.
          |function toUint8Array(buf) {
          |  var u = new Uint8Array(buf.length);
          |  for (var i = 0; i < buf.length; ++i) {
          |    u[i] = buf[i];
          |  }
          |  return u;
          |}
          |// Loads a WebAssembly dynamic library, returns a promise.
          |// imports is an optional imports object
          |function loadWebAssembly(filename, imports) {
          |  // Fetch the file and compile it
          |  const buffer = toUint8Array(require('fs').readFileSync(filename))
          |  return WebAssembly.compile(buffer).then(module => {
          |    return new WebAssembly.Instance(module, imports)
          |  })
          |}
          |
          |var memory = new WebAssembly.Memory({initial:100});
          |var importObject = {
          |  system: {
          |    mem: memory,
          |
          |    printInt: function(arg) {
          |      console.log(arg);
          |      0;
          |    },
          |
          |    printString: function(arg) {
          |      var bufView = new Uint32Array(memory.buffer);
          |      var len = bufView[arg];
          |      var i = 0;
          |      var result = "";
          |      while(i < len) {
          |        result += String.fromCharCode(bufView[arg+i+1]);
          |        i = i + 1
          |      }
          |      console.log(result);
          |      0;
          |    }
          |
          |  }
          |};
          |
          |loadWebAssembly('$moduleFile', importObject).then(function(instance) {
          |""".stripMargin ++
          module.functions.filter(f => toRun(f) && f.args.isEmpty).map { f =>
      s"""|  instance.exports.${f.name}();""".stripMargin
          }.mkString("\n") ++
       """|}).catch( function(error) {
          |  process.exit(1)
          |})
          |""".stripMargin
    val fw = new FileWriter(new File(fileName))
    fw.write(wrapperString)
    fw.flush()
  }
}
