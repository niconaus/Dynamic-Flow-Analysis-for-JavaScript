# Dynamic-Flow-Analysis-for-JavaScript

This repository holds the source code for the analysis described in the paper "Dynamic Flow Analysis for JavaScript" by Nico Naus and Peter Thiemann.

This implementation is provided as is. It might contain bugs, and is definetely not production code. It is only meant to be used as proof of concept.

To execute the analysis, please download the Jalangi framework here:
https://github.com/Samsung/jalangi2

Then use for example NodeJS to run the analysis (see the Janangi page for more instructions).

This will look something like:

  node jalangi/src/js/commands/jalangi.js --inlineIID --inlineSource --analysis analysis/dti.js jalangi/tests/octane/raytrace.js

If you require more information, or want to report a bug, do not hesitate to contact me.
