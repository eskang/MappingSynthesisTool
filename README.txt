# Mapping Synthesizer

This document contains instructions for running the artifact for the
paper titled "Automated Synthesis of Secure Platform Mappings'' by
Eunsuk Kang, Stephane Lafortune, and Stavros Tripakis.

## Introduction

The Mapping Synthesizer is a tool that takes (1) a model of a
high-level design (e.g.,\ OAuth protocol), (2) a model of a low-level
platform (HTTP), (3) a specification of a partial mapping between the
two, and produces a maximal mapping constraint that describes how to
implement the design on the platform in a way that preserves a desired
high-level property. The input design and platform models are
specified in Alloy, a modeling language based on a first-order
relational logic. The synthesizer takes a counterexample-guided
inductive synthesis (CEGIS) approach and uses the Alloy Analyzer as
the underlying verification engine to generate valid mappings (i.e.,
those mappings that preserve the property).

## Installation instructions

All the necessary dependencies have already been installed on the
provided VM. However, if you wish to compile or run the Mapping
Synthesizer on a different machine, the following packages are
required:

- Java JDK 8 or higher
- Scala 2.12.8
- sbt 1.2.8 (build tool for Scala)

## Reproducing the case study results from the paper

Scripts have been created for running the Mapping Synthesizer with the
input parameters that were used for the two OAuth case studies in the
paper.

To reproduce the OAuth 1 cases tudy, run the following script in the
top-level MappingSynthesizer directory:

./synthesize_oauth1_mapping

To reproduce the OAuth 2 case study, run:

./synthesize_oauth2_mapping

In each case, the maximal symbolic mapping constraint will be output
into file "solution_mapping.out".

The Alloy Analyzer uses an off-the-shelf SAT solver for verification,
and the order in which the synthesizer traverses the space of
candidate mappings is likely to differ from machine to
machine. Therefore, the statistics for the synthesis task (e.g.,
number of mapping candidates explored before finding a solution, time
spent by the verifier, total synthesis time) may be different from
those reported in the paper.

## Directory structure

/models
  /alloy
    /oauth
    /generated
      /valid
      /invalid
/source
  /
  
## Running the Mapping Synthesizer:

The Mapping Synthesizer is a Java program that can be executed as a
Java application with four input parameters:

java -jar MappingSynthesizer.jar model_1 model_2 partial_mapping config

model_1: A description of the high-level design model 
model_2: A description of the low-level platform model
partial_mapping: A specification of a partial mapping from model_1 to model_2
config: A file containing various configuration parameters

## Input parameter descriptions

### Model files:

### Partial mapping specification:

### Config file:


## Compiling the Mapping Synthesizer:

The interactive Scala build tool, sbt, can be used to compile the
source code for the Mapping Synthesizer.

cd source
sbt compile


## Contact

Please send any questions or feedback to Eunsuk Kang (eskang@cmu.edu).

