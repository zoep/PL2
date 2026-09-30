# Installation Instructions for the Rocq Proof Assistant
TL;DR Install Rocq via opam, and the VSRocq extension for VS Code.

To do the course assignments, you will need the Rocq Proof Assistant installed (version >= 9.0.0), as well as an IDE with Rocq support. Rocq is available for Linux, MacOS and Windows.

## Rocq Installation

### Linux and MacOS

##### Installation with Opam (for experienced users - recommended)
Rocq can be installed via opam, the OCaml package manager. The instructions below are adapted from [here](https://coq.inria.fr/opam-using.html).

- Install OCaml and opam from [here](https://ocaml.org/install#linux_mac_bsd).
- If you already have opam installed, make sure that its version is >= 2.1.0.
```bash
# Make sure opam version is 2.1.0 or above.
opam --version
```
- After the installation, initialize opam with the following commands. The `opam init` command will ask you to allow opam to set up its initialization scripts; it is a good idea to accept, so that you do not have to initialize opam in every new shell.
```bash
opam init
eval $(opam env)
```
- To install Rocq, run the commands below. (This will take several minutes, as it builds Rocq from source):
```bash
# Update the package list, pin the version of Rocq, and install it.
opam update
opam pin add rocq-core 9.3.0
opam install rocq-prover
```
- Make sure that Rocq has been installed. The command below should run and print the version you just installed.

```bash
rocq -v
```

#### Binary Installation (for beginners)
This installation method is not recommended, unless you run into significant problems with the other methods. A binary installer exists only for MacOS with Apple Silicon, and you can download it from [here](https://github.com/rocq-prover/platform/releases/tag/2026.07.0). There is no binary installer for Linux or for MacOS with an Intel processor, so you will have to follow the opam installation.


### Windows

#### Binary Installation
You can install Rocq using the Windows installer that you will find [here](https://github.com/rocq-prover/platform/releases/tag/2026.07.0). This will also install RocqIDE, which provides an interactive environment for using the Rocq Proof Assistant. Although suboptimal, this solution will cover the needs of the course.

To check your installation, open RocqIDE and then the lecture `lectures/Rocq/notes_01_intro.v`. You should be able to run Rocq's interactive environment.


#### Installation Using WSL
If you use WSL (Windows Subsystem for Linux), you can install Rocq by following the instructions for Linux.


## Editors
To use Rocq interactively, you will need an IDE with Rocq support.

### Visual Studio Code (recommended)
The recommended way to edit Rocq files is through the [VSRocq](https://marketplace.visualstudio.com/items?itemName=rocq-prover.vsrocq) extension for VS Code.

- Install VS Code from [here](https://code.visualstudio.com/download).
- Install the Rocq LSP
```
opam install vsrocq-language-server
```
- Check that the installation above was successful:
```
which vsrocqtop
```
The command above should return the path of the executable you installed.

- Install the VsRocq extension for VS Code:

  - Open VS Code.
  - Press `F1` to open the command palette, type `Extensions: Install Extension` and press `enter`.
  - In the extension manager, search for VsRocq and press `enter` to open the VsRocq tab.
  - In the VsRocq tab, press `install`.
  - After the installation, go to the extension settings, which you will find by clicking the gear icon. In the `Vsrocq: Path` field, enter the full path returned by the `which vsrocqtop` command.

- You should now be able to open and interactively edit a Rocq file. Open the introductory lecture `lectures/Rocq/notes_01_intro.v` to make sure that the installation was successful. You can use the arrows to the right of the file name to step through the Rocq commands one by one. This lets you run each command interactively and watch how your proof evolves. When you are in proof mode, the state of your proof is shown in an auxiliary panel named `Rocq Goals`.


Tips:
- It is useful to get familiar with the key bindings. By going to `Code > Preferences > Keyboard Shortcuts` (or by typing Keyboard Shortcuts in the command palette (F1)) and searching for `Rocq:`, you can see the available VSRocq key bindings. Step forward and step backward are particularly useful. You can change them to something that suits you (e.g. `control+up` for step forward and `control+down` for step backwards).

- In the activity bar (which is, by default, on the left) you can click the Rocq Proof Assistant icon to open the query panel. This lets you run various queries to search for theorems or to see the types and definitions of symbols, as we will also see in class.


### Emacs
- You can download the emacs editor from [here](https://www.gnu.org/software/emacs/).

- To have an IDE for Rocq you will need [Proof General](https://proofgeneral.github.io). Follow the installation instructions in the Quick Installation section.

Tips:
- The `.emacs` file goes in your home directory.
- The shortcut `M-x` means `Alt-x` (Linux + Windows) or `Opt-x` (MacOS). More generally, the emacs "META key" is written as `M` and corresponds to `Alt` or `Option` depending on your system. `M-` means hold down the META key while typing. Similarly, the symbol `C` corresponds to the `Control` key.
- There are many emacs tutorials online. For example, see [here](https://www.stolaf.edu/people/humke/UNIX/emacs-tutorial.html#:~:text=The%20Emacs%20Tutorial&text=M%2D%20means%20hold%20the%20META,it%2C%20then%20type%20the%20character%20.).
- You will find the Proof General key bindings described [here](https://proofgeneral.github.io/doc/master/userman/Basic-Script-Management/#Script-processing-commands) and [here](https://proofgeneral.github.io/doc/master/userman/Coq-Proof-General/#Coq_002dspecific-commands) useful. Particularly useful are:

  - `C-c C-n`: step forward
  - `C-c C-u`: step backward
  - `C-c C-RET`: go to point
  - `C-c C-b`: go to end of file

### Vim
If you use Vim, you can install the [Coqtail](https://github.com/whonore/Coqtail) plugin. Coqtail needs the `coqidetop` executable, which is not installed by the instructions above. You can install it with the command:
```
opam install coqide-server
```

### RocqIDE
The binary installations of Rocq come with RocqIDE, an environment for interactive proofs with Rocq. You can find more information [here](https://rocq-prover.org/doc/V9.0.0/refman/practical-tools/coqide.html).
