# Caspots - Boolean network inference from time series data with perturbations

[![Gitter](https://badges.gitter.im/bioasp/community.svg)](https://gitter.im/bioasp/community?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

## Requirements

- python
- caspo >= 4
- clingo python module (https://github.com/potassco/clingo)
  On Ubuntu, install the clingo package.
- NuSMV >= 2.5 - http://nusmv.fbk.eu/NuSMV/download/getting-v2.html

## Installation

	pip install https://github.com/bioasp/caspots/archive/master.zip

This will install necessary dependencies, except the clingo python module and
NuSMV.

A docker image is also available

	docker pull bioasp/caspots

### Docker usage

The entry point of the docker image is the program `caspots`.
Hence you can run a image directly with `docker run`.
You can create an alias to use `caspots` command:

	alias caspots='docker run --rm --volume "$PWD":/wd --workdir /wd bioasp/caspots'

If you have multiple `caspots` command to run in the same directoy, it is
recommended to first create a container and then execute caspots commands in it.

	alias start-caspots='docker create --name caspots -it --volume "$PWD":/wd --workdir /wd --entrypoint=/bin/bash bioasp/caspots && docker start caspots'
	alias docker-caspots='docker exec caspots caspots'
	alias stop-caspots='docker stop caspots && docker rm caspots'

First type `start-caspots`, then use as many as `docker-caspots` calls you want.
Do not forget to call `stop-caspots` when the work is done.


## Usage

In the following, we assume that
* PKN.sif is the SIF description of the PKN delimiting the domain of BNs, e.g.:
    benchmarks/1/pkn1_cmpr.sif
* DATASET.csv is the MIDAS description of the multiplex dataset, e.g.,
    benchmarks/1/dataset1_cmpr_bn_1.csv
* RESULTS.csv is a CSV description of a set of Boolean Networks, as outputted by
  our python scripts.
* python is the python interpreter in version 2.7.X. On some systems, you should
  use python2.


To identify all Boolean Networks, call

	caspots identify PKN.sif DATASET.csv RESULTS.csv

By default, the identification will return the subset-minimal BNs.
Add --family all to compute _all_ the BNs.
Add --family mincard to compute the cardinal-minimal BNs.

The option --true-positives invokes a model-checker (NuSMV) to ensure that only true
positive BNs are returned. The true positive rate is then displayed.
If the PKN is not compatible with the data, the estimated difference of MSE with
minimal MSE is displayed.

The minimal estimated MSE is obtained with

	caspots mse PKN.sif DATASET.csv

The option --check-exacts invokes a model-checker (NuSMV) until it finds a BN
and a trace with the estimated MSE: in such a case, the displayed MSE is the
actual minimal MSE of the PKN with respect to the dataset.

The option --control-nodes allows the user to specify nodes that Caspots doesn't have to explain, they'll still be used to infer networks.
Important note: as of now the control nodes must be specified at time point 0 in the MIDAS file.

#### Authors
- Max Ostrowski
- Loïc Paulevé
- Anne Siegel
- Carito Guziolowski
