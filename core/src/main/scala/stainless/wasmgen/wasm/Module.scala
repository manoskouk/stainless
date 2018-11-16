package stainless
package wasmgen
package wasm

import Definitions._

// A WebAssembly module
case class Module(
  name: Label,
  imports: Seq[Import],
  globals: Seq[ValDef],
  table: Table,
  functions: Seq[FunDef]
) {

  import java.io.{File, FileWriter}

  def writeWasmText(fileName: String): Unit = {
    val fw = new FileWriter(new File(fileName))
    fw.write(ModulePrinter(this))
    fw.flush()
  }

  def writeNodejsWrapper(fileName: String, moduleFile: String): Unit = {
    val wrapperString =
      s"""// `Wasm` does **not** understand node buffers, but thankfully a node buffer
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
         |var rl = require('readline').createInterface({
         |  input: process.stdin,
         |  output: process.stdout
         |});
         |
         |function waitInput() {
         |  input = "";
         |  done = false;
         |  rl.resume();
         |  rl.on('line', function(answer) {
         |    rl.pause();
         |    input = answer;
         |    done = true
         |  });
         |  require('deasync').loopWhile(function(){return !done;});
         |  return input;
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
         |      var bufView = new Uint8Array(memory.buffer);
         |      var i = arg;
         |      var result = "";
         |      while(bufView[i] != 0) {
         |       result += String.fromCharCode(bufView[i]);
         |       i = i + 1
         |      }
         |      console.log(result);
         |      0;
         |    },
         |
         |    readInt: function() {
         |      var res = parseInt(waitInput());
         |      if (isNaN(res)) {
         |        console.log("Error: Could not parse int");
         |        process.exit(1)
         |      } else {
         |        return res
         |      }
         |    },
         |
         |    // This function has a weird signature due to restrictions of the current WASM format:
         |    // It takes as argument the position that it needs to store the string to,
         |    // and returns the first position after the new string.
         |    readString0: function(memB) {
         |      var s = waitInput();
         |      var size = s.length;
         |      var padding = 4 - size % 4;
         |      var fullString = s + "\0".repeat(padding);
         |      var newMemB = memB + size + padding;
         |      var bufView8 = new Uint8Array(memory.buffer);
         |      for (var i = 0; i < fullString.length; i++) {
         |        bufView8[memB + i] = fullString.charCodeAt(i);
         |      }
         |      return newMemB;
         |    }
         |
         |  }
         |};
         |
         |loadWebAssembly('$moduleFile', importObject).then(function(instance) {
         |""".stripMargin ++
      functions.filter(_.args.isEmpty).map { f =>
        s"  instance.exports.${f.name}();\n"
      }.mkString ++
       """  rl.close();
         |}).catch( function(error) {
         |  rl.close();
         |  process.exit(1)
         |})
         |""".stripMargin
    val fw = new FileWriter(new File(fileName))
    fw.write(wrapperString)
    fw.flush()
  }
}
