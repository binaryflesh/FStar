module OPLSS.Flag

val flag : Type u#0

val reveal : flag -> GTot bool

val branch : f:flag -> b:bool{ b == reveal f }