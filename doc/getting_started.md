Getting Started Guide
=====================

Our artefact comes as `slicer.ova` file, which is in Open Virtual Appliance
format supported by most virtualization software.  Use your favourite
virtualization solution (VirtualBox, VMWare) to import slicer.ova file.
Provided virtual machine comes with GHC 8.0.2 and all the libraries required to
compile our program.  After booting up the virtual machine log in as "user" with
password "user".  You will be automatically taken to `/home/user/slicer/`
directory containing source code of our submission and a its pre-compiled
version.  You should now see the README.md:

  less README.md

Begin reading starting from "Usage" section.  "Installation" has already been
performed so you can skip that section.

Root password for the virtual machine is "icfp2017".

Alternatively, if you don't want to use a virtual machine, go to

  https://github.com/jstolarek/slicer/

and follow `Installation` section of README.md (but skip step 2 for now - see
Disclaimer below).


Step-by-step instructions
=========================

Please follow "Reproducing examples from the paper" section of README.md


Disclaimer
==========

This file is intentionally kept very short because all the relevant
instructions are stored inside the virtual machine and the project files.

If the artefact is accepted we will create an `icfp2017-final` tag in the
repository to mark the accepted submission and update the virtual machine
accordingly.  This tag is already being referred to in step (2) of
`Installation` section of README.md - please ignore that for now.
