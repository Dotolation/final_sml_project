# SML -> JVM Compiler. 
This is a JVM compiler for a SML (Standard ML). 
Some of the codes were written with help of the instructor (skelecton code), but ```compiler.sml``` is my work. 

# How to run 

## This code was designed to be executed in Linux environment. 

- First, make the driver file using the below command.
```
make driver
```

- Once the driver is created, compile the an sml code using the below command line. 
```
./driver compile f
```
where ```f``` is an sml file to be converted. 
This will run ```doCompile``` method of the ```driver.sml```. 
The resulting output of the command is ```f.j```, a JVM bytecode file. 

