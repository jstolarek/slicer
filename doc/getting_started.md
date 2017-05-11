Getting Started Guide
=====================

Our artifact comes as `slicer-icfp2017.ova` file, which is in Open Virtual
Appliance format supported by most virtualization software.  Use your favourite
virtualization solution (VirtualBox, VMWare) to import `slicer-icfp2017.ova`
file.  Our software is written in Haskell.  Provided virtual machine comes with
GHC 8.0.2 and all the libraries required to compile our program.  After booting
up the virtual machine log in as "user" with password "user".  You will be
automatically taken to `/home/user/slicer/` directory containing source code of
our submission and a its pre-compiled version.  You should now look at the
README.md:

  less README.md

Begin reading starting from "Usage" section.  "Installation" has already been
performed so you can skip that section.

Root password for the virtual machine is "icfp2017".

Alternatively, if you don't want to use a virtual machine, go to

  https://github.com/jstolarek/slicer/tree/icfp2017

and follow `Installation` section of README.md.


Step-by-step instructions
=========================

Please follow "Reproducing examples from the paper" section of README.md


Disclaimer
==========

This file is intentionally kept short because all the relevant instructions are
stored inside the virtual machine and the project files.  (In fact, this file
repeats some of these instructions.)

GitHub repository contains `icfp2017` tag that is intended to mark the final
accepted version of our submitted code.  We recognize that evaluating the
artifact might require us to update our implementation.  In such a cse we will
update the repository tag.  (Well, delete the existing one and create a new one
with identical name - since tags can't be updated.)
