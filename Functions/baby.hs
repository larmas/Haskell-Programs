doubleMe x = x + x

cuadrado x = x * x

doubleUs x y = doubleMe  x + doubleMe y -- eis iqual dobleUs x y = x * 2 + y * 2

doubleSmallNumber x = if x > 100 
											then x 
											else x * 2

doubleSmallNumber' x = (if x > 100 then x else x * 2) + 1

ezequiel = "Hola me llamo Ezequiel Esteban Agustin de Kelops Depetris"

lastNumbers = [2,8,15,16,23] -- this is iqual to write "let lastNumbers = [2,8,15,16,23]" on terminal
