import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

/--
EJERCICIO 1: Racionalización de 1/√7
Objetivo: Demostrar que (1 / √7) = (√7 / 7) mediante pasos manuales.
-/
-- 'theorem' declara lo que vamos a demostrar. Le damos un nombre.
theorem racionalizacion_raiz_siete : (1 / Real.sqrt 7) = (Real.sqrt 7 / 7) := by
  -- 'have' crea un pequeño paso intermedio o lema local. Lo llamamos 'h7_pos'.
  have h7_pos : (0 : ℝ) < 7 := by
    -- 'positivity' es una táctica automática que dice: "es obvio que 7 es positivo".
    positivity
  -- Aquí creamos otro lema: 'h7_nonneg'. Afirmamos que 0 es menor o igual (≤) a 7.
  have h7_nonneg : (0 : ℝ) ≤ 7 := le_of_lt h7_pos
  -- Siguiente lema: Demostrar que la raíz de 7 no es cero
  -- (para poder dividir entre ella luego).
  have h_sqrt_neq_zero : Real.sqrt 7 ≠ 0 := by
    -- 'Real.sqrt_pos.2' dice: "Si x > 0, entonces la raíz de x > 0".
    -- El sufijo '.ne'' convierte el "mayor que cero" en "distinto de cero".
    exact (Real.sqrt_pos.2 h7_pos).ne'
  -- Guardamos la identidad clave de la raíz cuadrada en 'h_raiz'.
  have h_raiz : Real.sqrt 7 * Real.sqrt 7 = 7 := by
    -- 'Real.mul_self_sqrt' es el teorema que dice: √x * √x = x.
    -- Exige que demostremos que x no es negativo, por eso le pasamos 'h7_nonneg'.
    exact Real.mul_self_sqrt h7_nonneg
  -- 'calc' inicia un bloque de igualdades lógicas paso a paso.
  calc
    (1 / Real.sqrt 7) = (1 / Real.sqrt 7) * 1 := by
      -- Paso 1: Multiplicar por 1 no cambia nada (mul_one).
      rw [mul_one]
    _ = (1 / Real.sqrt 7) * (Real.sqrt 7 / Real.sqrt 7) := by
      -- Paso 2: Reemplazamos ese '1' por (√7 / √7) (div_self).
      rw [div_self h_sqrt_neq_zero]
    _ = (1 * Real.sqrt 7) / (Real.sqrt 7 * Real.sqrt 7) := by
      -- Paso 3: Multiplicamos numeradores y denominadores.
      rw [div_mul_div_comm]
    _ = Real.sqrt 7 / (Real.sqrt 7 * Real.sqrt 7) := by
      -- Paso 4: Simplificamos el numerador. 1 * √7 es simplemente √7.
      rw [one_mul]
    _ = Real.sqrt 7 / 7 := by
      -- Paso 5: Resolvemos el denominador usando la identidad 'h_raiz'.
      rw [h_raiz]
