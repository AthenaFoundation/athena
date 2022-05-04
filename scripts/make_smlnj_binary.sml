 CM.make("sources.cm");
 SMLofNJ.exportFn("athena_image",fn (_,arg1::_) => (Athena.runWithStarterFileAndQuit(SOME(arg1)); OS.Process.success));