
# README

This is the artifact for the paper *Reducing Over-Synchronization in JavaScript Applications*.


## Setup and build docker image 

Make sure you have docker installed.

#### If you don't have the image:

Then, from the root of the repo, you can build and run the docker image.
```
# build
docker build -t resynchronizer . 
```

#### If you do have the image

Download the image, and load it:
```
docker load -i resynchronizer.tgz # assuming image file resynchronizer.tgz
```

## Usage

Run the docker:
```
./runDocker.sh
```

Now, you'll be in the `/home/resynchronizer` directory of the docker image.


In the docker, you can 
* interact with our data, and reproduce the graphs from the paper (or construct similar graphs we did not include in the paper)
* run Resynchronizer on a new project
* check out the transformed projects we tested with and rerun the timing experiments

### Contents of the container

The relevant contents of the container are as follows:
* `ExperimentalData`: data from our timing experiments; can be used to reproduce the graphs in the paper and supplementary materials
* `DataAnalysis` directory: contains a jupyter notebook for interacting with our data
* `Resynchronizer` directory: contains the code for applying and running Resynchronizer
* `Resynchronizer/ReorderingUtils.qll`: static side effect analysis code
* `Resynchronizer/reorder_me.py`: the driving script for applying the reorderings determined through the analysis
* `Resynchronizer/applyResync.sh`: script for applying Resynchronizer to a project
* `Paper` directory: paper and associated supplementary materials


### Interacting with data: graph reproduction

The `ExperimentalData` directory contains all the raw timing data from our experiments.
To reproduce the graphs in the paper and further explore the data, go into the `DataAnalysis` directory and open the jupyter notebook:
```
cd DataAnalysis
jupyter notebook --ip 0.0.0.0 --no-browser --allow-root
```
This will produce some output, the last line of which will be of the form
```
http://127.0.0.1:8888/?token=<some string of chars>
```
Then, on your machine, you can access the notebook by copy pasting that path into your browser.

Alternatively, you can access the notebook by going to `http://127.0.0.1:8888/notebooks/data_analysis.ipynb` on your browser, and then entering the string of characters following `token=` from the docker output, when prompted for a token.

In the notebook, there are the following example commands to recreate the graphs from the paper.
For example:
```
pkgname = "kactus"

load_data_for_package(pkgname) 

# regenerate Figure 10 in the paper
scatterplot_test_speedup(comp_mean_table, pkgname) 

# regenerate Figure 11 in the paper
plot_test_times( bothswap_jest_tests, noswap_jest_tests, 117) 
```
Calling `load_data_for_package` with the name of another project will allow you to interact with that data instead.
Looking at the supplementary materials, here are a few other examples:
```
# second graph in Supplementary materials: section 3
load_data_for_package("webdriverio")
scatterplot_test_speedup(comp_mean_table, "webdriverio")


# first graph in Supplementary materials: section 4
load_data_for_package("kactus")
plot_test_times( bothswap_jest_tests, noswap_jest_tests, 22)
```

When you're done looking at the data, exit the notebook to try the rest of the artifact.


### Run resynchronizer on a new project

To use Resynchronizer, first enter the `Resynchronizer` directory  in the container home.

Demonstrative example of applying resynchronizer to the version of `mattermost-redux` used in our experiments:
```
git clone https://github.com/mattermost/mattermost-redux Playground/mattermost-redux
cd Playground/mattermost-redux
# checkout the specific commit we tested on (was most recent commit at the time)
git checkout dd44020f008f6e1955709ff7fc3e1c8c42388396
cd ../..

# set up the project
# note: this can differ per project, we have a general script that works in most cases but 
# depending on the build configuration of the project you want to test with, this may differ
./resetProject.sh Playground/mattermost-redux


# now, apply resynchronizer
./applyResync.sh Playground/mattermost-redux/ QLDBs/mattermost-redux

```
The `mattermost-redux` with the reorderings applied is now saved in the directory `reordered_proj` in `/home/resynchronizer` (your current directory).

To see the effect of the transformations, `grep` for the temporary variables:
```
cd reordered_proj
grep -rn "TEMP_VAR_AUTOGEN"
```
You should see the following output:
```
src/client/client4.ts:1047:var TIMING_TEMP_VAR_AUTOGEN287__RANDOM = perf_hooks.performance.now();
src/client/client4.ts:1048: var AWAIT_VAR_TIMING_TEMP_VAR_AUTOGEN287__RANDOM = await  this.doFetchWithResponse(
src/client/client4.ts:1052:console.log("/home/resynchronizer/reordered_proj/src/client/client4.ts& [719, 8; 722, 10]& TEMP_VAR_AUTOGEN287__RANDOM& " + (perf_hooks.performance.now() - TIMING_TEMP_VAR_AUTOGEN287__RANDOM));
src/client/client4.ts:1053: const {response} =  AWAIT_VAR_TIMING_TEMP_VAR_AUTOGEN287__RANDOM
src/actions/admin.ts:1007:var TEMP_VAR_AUTOGEN263__RANDOM =  Client4.sendWarnMetricAck(warnMetricId, forceAck);
src/actions/admin.ts:1012:var TIMING_TEMP_VAR_AUTOGEN263__RANDOM = perf_hooks.performance.now();
src/actions/admin.ts:1013: await  TEMP_VAR_AUTOGEN263__RANDOM
src/actions/admin.ts:1014:console.log("/home/resynchronizer/reordered_proj/src/actions/admin.ts& [656, 12; 656, 68]& TEMP_VAR_AUTOGEN263__RANDOM& " + (perf_hooks.performance.now() - TIMING_TEMP_VAR_AUTOGEN263__RANDOM));
src/actions/search.ts:511:var TEMP_VAR_AUTOGEN152__RANDOM =  Client4.searchPosts(teamId, terms, true);
src/actions/search.ts:516:var TIMING_TEMP_VAR_AUTOGEN152__RANDOM = perf_hooks.performance.now();
src/actions/search.ts:517: var AWAIT_VAR_TIMING_TEMP_VAR_AUTOGEN152__RANDOM = await  TEMP_VAR_AUTOGEN152__RANDOM
src/actions/search.ts:518:console.log("/home/resynchronizer/reordered_proj/src/actions/search.ts& [298, 12; 298, 67]& TEMP_VAR_AUTOGEN152__RANDOM& " + (perf_hooks.performance.now() - TIMING_TEMP_VAR_AUTOGEN152__RANDOM));
src/actions/search.ts:519: posts =   AWAIT_VAR_TIMING_TEMP_VAR_AUTOGEN152__RANDOM

```
Here you see the newly introduced variables assigned to the computation that was originally being awaited, with:
```
var TEMP_VAR_AUTOGEN<number> = ...
```
You can also see where the results are awaited: 
```
await TEMP_VAR_AUTOGEN<number>
```

The other results of the `grep` are the `TIMING_TEMP` variables, which are only introduced for the purposes of logging how long the awaited computations are taking (you see these variables in the `console.log` calls).

If you want to run the tests of `mattermost-redux` and observe the printing of the timing tracking statements:
```
npm run test
```
Then, go back to the `/home/resynchronizer` directory to go to the next step.

### Rerunning timing experiments

The transformed projects are available on github: we forked them and created branches with the reorderings applied (called ReorderingApplied).

For example, to check out the reordered version of `mattermost-redux` that contains the experiment scripts:
```
git clone --branch ReorderingApplied https://github.com/emarteca/mattermost-redux.git 
```

This version of the repo contains the reorderings, all the scripts required to run the experiments, and the list of tests affected by the reorderings.


Before running experiments, you must set up and build the project:
```
./resetProject.sh mattermost-redux


# standardize the paths of the tests to match those in the docker container
# (when cloned, they match the original paths on the computer where I ran the experiments)
./dockerize_paths.sh mattermost-redux
```

Then, you can run the experiments.
```
cd mattermost-redux
./batchListOfTests.sh 50 test_list.txt raw_output.out test_times_bothswap_50times.out 5
```
The parameters are:
* `50`: the number of test iterations
* `test_list.txt`: the pre-generated list of tests affected by the reorderings
* `raw_output.out`: the raw logged output of all the tests, that gets processed into the next file
* `test_times_bothswap_50times.out`: the file where the processed test output gets dumped; this matches `ExperimentalData/mattermost-redux/test_times_bothswap_50times.out` (although of course the exact numbers will differ since they are test runtimes)
* `5`: the number of warmup runs

If you want to only run a few test iterations to make sure it's working, I would recommend setting a smaller number of test iterations (maybe 10) and omitting the warmup runs (if the warmup run argument is omitted it defaults to 0).

You can also run the experiments on the non-reordered code by checking out the `JustTiming` branch (where all awaits that will be reordered are timed):
```
git checkout JustTiming
```
Then, rerun the experiments the same way as above.
Change the output filename to `test_times_noswap_50times.out` to emulate the experiments we performed.

**Note**: the timing values will be different running here than in the reported results in the paper, since those were not run inside a docker container. 



## Thanks!
Let us know if you run into any issues or have any questions!


