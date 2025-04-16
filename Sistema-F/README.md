# Sistema-F

Para ejecutar el proyecto.
1- 
    stack setup
2- 
    stack build 
3- 
    stack exec Sistema-F-exe

El setup solo se ejecuta una sola vez, ante cualquier cambio en el código se debe, ejecutar de nuevo la linea stack build antes de el stack exec.

Para ejecutar la documentación de haddock se puede con:
    stack haddock --no-haddock-deps --open

o si no con
    stack haddock --open Sistema-F