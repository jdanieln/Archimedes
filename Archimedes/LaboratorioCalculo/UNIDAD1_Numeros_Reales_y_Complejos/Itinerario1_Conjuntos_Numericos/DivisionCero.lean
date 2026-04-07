import Mathlib.Data.Real.Basic

/--
TEOREMA: Consecuencia algebraica de una ecuación de la forma `a = b * 0`.

Este teorema demuestra que, si un número real `a` es igual a `b * 0`,
entonces necesariamente `a = 0`.

La idea es directa:
- por la hipótesis, `a = b * 0`;
- pero todo número real multiplicado por `0` es `0`;
- por tanto, `a = 0`.

Observación importante:
este resultado no formaliza por sí solo la "indefinición" de la división
por cero en el sentido usual de las matemáticas. Lo que sí establece es
una consecuencia estructural básica: cualquier ecuación de la forma
`a = b * 0` fuerza a que `a` sea cero.

Esto permite distinguir dos situaciones clásicas:
1. Si `a ≠ 0` (por ejemplo, pensar en `12 = b * 0`), se obtiene una contradicción,
   porque ningún `b` puede hacer verdadera la ecuación.
2. Si `a = 0` (por ejemplo, `0 = b * 0`), la ecuación sí es verdadera para muchos
   valores de `b`, así que no hay unicidad.
-/
theorem consecuencia_division_cero (a b : ℝ) (h : a = b * 0) : a = 0 := by
  -- Usamos `calc` para encadenar igualdades paso a paso.
  calc
    -- Paso 1: partimos de la hipótesis dada.
    a = b * 0 := h
    -- Paso 2: simplificamos `b * 0` usando que todo número por cero es cero.
    _ = 0     := mul_zero b
