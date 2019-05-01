# Mapping Synthesizer

This document contains instructions for running the artifact for the paper titled "Automated Synthesis of Secure Platform Mappings'' by Eunsuk Kang, Stephane Lafortune, and Stavros Tripakis.

## Introduction

The Mapping Synthesizer is a tool that takes (1) a model of a high-level design (e.g.,\ OAuth protocol), (2) a model of a low-level platform (HTTP), (3) a specification of a partial  mapping from the high-level model to the low-level one, and produces a maximal mapping constraint that describes how to implement the design on the platform in a way that preserves a desired high-level property of the system. The input design and platform models are specified in Alloy, a modeling language based on a first-order relational logic. The synthesizer takes a counterexample-guided inductive synthesis (CEGIS) approach and uses the Alloy Analyzer as the underlying verification engine to generate valid mappings (i.e., those mappings that preserve the property). 

## Installation instructions

All the necessary dependencies have already been installed on the provided VM. However, if you wish to compile or run the Mapping Synthesizer on a different machine, the following packages are required:

- Java JDK 8 or higher
- Scala 2.12.8
- sbt 1.2.8 (build tool for Scala)

## Reproducing the case study results from the paper

Scripts have been created for running the Mapping Synthesizer with the set of input parameters that were used for the two OAuth case studies described in the paper.

To reproduce the OAuth 1 cases tudy, run the following script in the top MappingSynthesizer directory:

./synthesize_oauth1_mapping

To reproduce the OAuth 2 case study, run:

./synthesize_oauth2_mapping

In each case, the maximal symbolic mapping constraint will be output into file "solution_mapping.out".

Since the Alloy Analyzer uses an off-the-shelf SAT solver for verification, the order in which the synthesizer traverses the space of candidate mappings is likely to differ from machine to machine, and thus, the results produced may be different from those reported in the paper.

## Running the Mapping Synthesizer:

java -jar MappingSynthesizer.jar


## Directory structure

/models
  /alloy
    /oauth
    /generated
/source
  /

## Compiling the Mapping Synthesizer:


