# MappingSynthesis
This repository contains the source code for a prototype implementation of the Mapping
Synthesis tool, which takes (1) a pair of event-based behavioral
models (one depicting a high-level design and another a low-level
platform) (2) a property of the high-level design, and (3) produces a
mapping from the high-level model to the low-level one ensuring that
the satisfaction of the given property.

More details about the synthesis problem and the procedure is
described in the following report:

http://arxiv.org/abs/1705.03618

## Structure

* /libs: Native libraries for SAT solvers used by the verifier
(currently, Alloy Analyzer).
* /models: Models provided as inputs to the synthesizer.
* /src: Source code for the synthesizer.
* /util: Auxiliary tools.
	* parsepan: Used to parse verifier results from SPIN.

## Setup

The simplest way to build and execute the synthesizer is by using the
Scala IDE, which is available to download for free:

http://scala-ide.org/

Once inside the IDE, create a new Scala project and import the source files
(/src). The project relies on native libraries for SAT solvers
(used by the Alloy Anayzer). These libraries reside in /libs, but the
directory location must be added to the project build path; in the
IDE, this can be modified through the project "Properities" -> "Java Build Path" -> "Source" -> "Native library location".

The main entry functions for the tool is located in "/src/synthesis/Synthesizer.scala".

## Contact

Please send any questions or comments to Eunsuk Kang (eunsuk.kang@berkeley.edu).


