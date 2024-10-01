# Bonn Lean Course WiSe 24/25

## In this repository

You will find the Lean files in the `LeanCourse` directory:
* The `Lectures` folder contains all lectures
* The `Assignments` folder contains the assignments that you have to hand in via eCampus
* The `MIL` folder contains the exercises from the book Mathematics in Lean. You can find the textbook online here:
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
(or as a
[pdf document](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf)).

## Installation

* You have to install Lean, and two supporting programs: Git and VSCode. Follow these [instructions](https://docs.lean-lang.org/lean4/doc/quickstart.html) to do this.

* This will guide you to install VSCode (a text editor which supports Lean), git (a version control system) and elan (the Lean package manager).

* In the step **Set up Lean 4 project** click on **Download an existing project** (third bullet point). As the URL of the repository, use `https://github.com/fpvandoorn/LeanCourse24` and then select a folder where you want to download this repository.

* To test that everything is working, open the repository and open the file `LeanCourse/Test.lean`.
The file should be ready a few seconds later. If you see a blue squiggle under `#eval`, Lean is running correctly.

* A useful (but optional) extension is the VSCode extension `Error Lens`. If you install this, you will see messages from Lean right in the file where you're typing.
Optional: ErrorLens


## Troubleshooting

Note: To get this repository, you will need to download Lean's mathematical library, which takes about 5 GB of storage space.

It might be tricky to get Lean running on a laptop that is more than 10 years old or on a chromebook, since Lean does use a moderate amount of recourses.
You can still run Lean in your browser by using Codespaces or Gitpod, see the the instructions at the bottom of this file.

* If you get errors such as `curl: (35) schannel` or `uncaught exception: no such file or directory (error code: 2)` take a look [here](https://leanprover-community.github.io/install/project.html#troubleshooting).

<!-- If you don't have a suitable laptop, ask the instructor Lean on a university computer, make sure to use the `fmath` local user, and ask the teacher for the password. Then run `install_lean` in a terminal and follow the steps under `Get the course repository`. -->
<!--
### Get new exercises

If you have already followed the steps above, and want to get the latest exercises, open a terminal in your local copy of this repository (e.g. `cd LeanCourse24`) and then run `git pull`. This gives you the new exercises.

**Update Nov 7**: I updated the version of mathlib used in this project. This time, after running `git pull` do the following:
* Close VSCode (if you have it open)
* In your terminal, in the `LeanCourse24` folder, run `lake exe cache get!` (or `~/.elan/bin/lake exe cache get!` if `lake` cannot be found).
* Wait until the command finishes with downloading and decompressing. If you get an error, run it again.
* Now you can reopen VSCode and Lean should work again. -->

## Temporary ways to use Lean

You can temporarily use Codespaces or Gitpod if you have trouble installing Lean locally.

### Using Codespaces

You can temporarily play with Lean using Github codespaces. This requires a Github account, and you can only use it for a limited amount of time each month. If you are signed in to Github, click here:

<a href='https://codespaces.new/fpvandoorn/LeanCourse24' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

* Make sure the Machine type is `4-core`, and then press `Create codespace`
* After 1-2 minutes you see a VSCode window in your browser. However, it is still busily downloading mathlib in the background, so give it another few minutes (5 to be safe) and then open a `.lean` file to start.

### Using Gitpod

Gitpod is an alternative to codespaces that is slightly inconvenient, since it requires you to verify your phone number.

Click this button to get started:

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/fpvandoorn/LeanCourse24)

This creates a virtual machine in the cloud,
and installs Lean and Mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get!` as above.

Gitpod gives you 50 free hours every month.
When you are done working, choose `Stop workspace` from the menu on the left.
The workspace should also stop automatically
30 minutes after the last interaction or 3 minutes after closing the tab.

To restart a previous workspace, go to [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).
