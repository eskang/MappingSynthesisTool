# Mapping Synthesizer

This document contains instructions for running the artifact for the
paper titled "Automated Synthesis of Secure Platform Mappings'' by
Eunsuk Kang, Stephane Lafortune, and Stavros Tripakis.

This document is best displayed using a Markdown viewer.

## Introduction

The Mapping Synthesizer is a tool that takes (1) a model of a
high-level design (e.g., OAuth protocol), (2) a model of a low-level
platform (HTTP), (3) a specification of a partial mapping between the
two, and produces a maximal mapping constraint that describes how to
implement the design on the platform in order to preserve a desired
high-level property. The input design and platform models are
specified in Alloy, a modeling language based on a first-order
relational logic. The synthesizer takes a counterexample-guided
inductive synthesis (CEGIS) approach and uses the Alloy Analyzer as
the underlying verification engine to generate valid mappings (i.e.,
those mappings that preserve the property).

## Installation instructions

The Mapping Synthesizer requires Java JDK 8 or higher. In the vanilla CAV2019
VM, this package can be installed by:

	sudo apt-get install openjdk-8-jre-headless

## Reproducing the case study results from the paper

Scripts have been created for running the Mapping Synthesizer with the
input parameters that were used for the two OAuth case studies in the
paper.

To reproduce the OAuth 1 cases tudy, run the following script in the
top-level MappingSynthesizer directory:

	./synthesize_oauth1_mapping

To reproduce the OAuth 2 case study, run:

	./synthesize_oauth2_mapping

In each case, the synthesized maximal mapping constraint will be
output into a file named `solution_mapping.als`, an Alloy model that
encodes the synthesized mapping as logical constraints in the
predicate `mappingConstraints` (located at the bottom of the file).

The Alloy Analyzer uses an off-the-shelf SAT solver for verification,
and the order in which the synthesizer traverses the space of
candidate mappings is likely to differ from machine to
machine. Therefore, the statistics for the synthesis task (e.g.,
number of mapping candidates explored before finding a solution, time
spent by the verifier, total synthesis time) may be different from
those reported in the paper.

## Directory structure

* `/`: Top-level directory. Contains MappingSynthesis.jar and input files
    for the OAuth case studies (oauthx.model, httpx.model,
    oauthx.mapping, oauthx.config where x = 1 or 2).

* `/models`
* `/models/alloy/oauth`: Alloy models of the OAuth protocols and HTTP.
* `/models/alloy/generated`: Alloy (.als) files containing explored mappnigs.
* `/models/alloy/generated/valid`: Valid mapping constraints
  synthesized, including non-maximal ones that the tool explores
  during the generalization step.
* `/models/alloy/generated/invalid`: Invalid mapping constraints
  explored by the tool.

## Running the Mapping Synthesizer:

The Mapping Synthesizer is a Java program that can be executed as a
Java application with four input parameters:

	java -jar MappingSynthesizer.jar model_1 model_2 partial_mapping config

where:

* `model_1`: A description of the high-level design model 
* `model_2`: A description of the low-level platform model
* `partial_mapping`: A specification of a partial mapping from model_1 to model_2
* `config`: A file containing various configuration parameters

For example, to run the OAuth 1.0 case study, type:

	java -jar MappingSynthesizer.jar oauth1.model http1.model oauth1.mapping oauth1.config

To run OAuth 2.0, type:

	java -jar MappingSynthesizer.jar oauth2.model http2.model oauth2.mapping oauth2.config

To run OAuth 2.0 with a more constrained partial mapping (i.e., a smaller
number of candidate mappings to search), type:

	java -jar MappingSynthesizer.jar oauth2.model http2.model oauth2-reduced.mapping oauth2.config

## Input parameter descriptions

Each input file is a Scala program fragment that is dynamically
evaluated by the Mapping Synthesizer.

### Model files:

Each model file contains declarations of (1) abstract labels and their
concrete counterparts, (2) datatypes that constitute the parameters of
those labels, and (3) instances (i.e., specific values) of those
datatypes. These declarations are made using the following API functions:

* `Store.mkBasicDatatype(name: String, parentType: Type)`: Create a
  named datatype that belongs to a parent type.

* `Store.mkValue(name: String, type: Type)`: Create a named value that
  belongs to the specified type.

* `Store.mkLabel(name: String, params: Map[String,Type], returnParams:
  Set[String], procID: Int)`: Create a named label with (1) a set of
  parameters, specified as a map from names to their types, (2) a set
  of return parameters, specified as a subset of the parameter names
  in `params`, and (3) an integer value that represents a particular
  process to which this label is assigned.

### Partial mapping specification:

Each partial mappping specification file defines a set of user-defined
constraints
between a pair of abstract and concrete labels, using the following
API functions:

* `addEqualConstraints(constraints : Map[String, String])`:
  For each entry (a, b) in the map `constraints`, add a constraint of
  form `a = b`.

* `addNotEqualConstraints(constraints:
Map[String, String])`:
For each entry (a, b) in the map `constraints`, add a constraint of
  form `!(a = b)`.

* `addConditionalConstraints(constraints:
  Map[Constraint, Constraint])`: For each entry (a, b) in the map `constraints`, add a constraint of
  form `a => b`.

### Config file:

* `DIR_MODEL`: Directory that contains high-level design and platform models in Alloy.
* `PATH_TEMPLATE`: Path to the single Alloy model that imports a pair
  of high-level design and platform models. This file will be used as a
  basic template to synthesize a new Alloy model with a complete
  mapping constraint.
* `DIR_GENERATED`: Directory that will contain mapping files generated
  during the search by the Synthesizer.
* `PREFIX_GENERATED`: Prefix for the generated mapping files.

### Property specification:

Our tool supports two types of properties: reachability (i.e., whether
a mapping allows certain desirable behaviors in the resulting
implementation) and safety (whether a mapping introduces undesirable
behaviors in the implementation). These properties are specified as
predicates `mappingReachability` and `mappingSafety`, respectively, in
the Alloy model that is located in `PATH_TEMPLATE` in the
configuration file.

## Source

The source code for the tool is available at https://github.com/eskang/MappingSynthesisTool

## Contact

Please send any questions or feedback to Eunsuk Kang (eskang@cmu.edu).

