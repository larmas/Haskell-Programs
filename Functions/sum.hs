divisores::Int->[Int]
divisores 0 = []
divisores n = [ y | y <- [1..n-1], mod n y == 0]

suma::[Int]->Int
suma [] = 0
suma (x:xs) = x+suma xs

perf::Int->Bool
perf n = n== suma (divisores n)