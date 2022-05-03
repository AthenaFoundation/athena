These files in this directory provide Athena code for each of the
chapters of

  Konstantine Arkoudas and David Musser
  Fundamental Proof Methods in Computer Science
  A Computer Based Approach

for use in experimenting with the chapter's examples and developing
solutions to the chapter's exercises.

Most exercises depend on some of the definitions, declarations,
theorems, etc. that are defined in the book preceding the point where
the exercise appears. Each chapter file includes the needed material
within the file or loads it from the Athena library or from included
supplementary files. So one way to work with the file is to load it
(or a copy of it) into a text editor, write your solution within the
file at the point of the exercise, and test it by loading the file
into Athena. Alternatively, load just the part of the file up to the
point of the exercise and then work on the solution in Athena’s
interactive mode.
 
Some of the theorems proved in exercises are assumed to be available
for use as lemmas in examples or solutions to exercises that appear
farther on in the file. Thus it might seem that one must work on
exercises in sequential order, and the file might not be fully
loadable until all proofs called for have been supplied. To provide
for greater flexibility, we have arranged that the files are fully
loadable from the beginning and exercises can be tackled in any order:

- For some of the chapters, exercise solutions are provided in
supplementary files and are loaded by the chapter file. To solve the
exercise, delete the load command and write in its place your own
solution. (If you copy the chapter file to a different directory to
work on it, you’ll need to also copy its accompanying subdirectory of
solution files.)

- In other chapters we have simply inserted “stopgap proofs”:
(!stopgap T) enters sentence T into the assumption base as though it
had been actually proved, thus treating it as a theorem. To solve the
exercise, delete the stopgap call and write in its place a real proof
of T.  (stopgap is just another name for force, the top-down
proof-development aid described in Section 4.7 of the book. We use
stopgap instead of force to distinguish such uses from other uses of
force, such as presenting and using a theorem before the point where
it is actually proved. Such uses of force in the files don’t need to
be replaced.)

In exercises that call for a definition instead of a proof, we
sometimes provide some of the structure of the definition, but
commented out. After uncommenting those lines, finish the exercise by
replacing any use of “...” with actual code.


