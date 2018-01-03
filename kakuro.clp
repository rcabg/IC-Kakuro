;;; IC: Trabajo (2016/2017)
;;; ResoluciÃ³n deductiva de un Kakuro
;;; Departamento de Ciencias de la ComputaciÃ³n e Inteligencia Artificial
;;; Universidad de Sevilla
;;;============================================================================


;;;============================================================================
;;; RepresentaciÃ³n del Kakuro
;;;============================================================================

;;;   Utilizaremos la siguiente plantilla para representar las celdas del
;;; Kakuro. Cada celda tiene los siguientes campos:
;;; - id: Identificador Ãºnico de la celda
;;; - fila: NÃºmero de fila en la que se encuentra la celda
;;; - columna: NÃºmero de columna en la que se encuentra la celda
;;; - rango: Rango de valores que se pueden colocar en la celda. Inicialmente
;;;   el rango son todos los valores numÃ©ricos de 1 a 9.

(deftemplate celda
  (slot id)
  (slot fila)
  (slot columna)
  (multislot rango
             (default (create$ 1 2 3 4 5 6 7 8 9))))

;;;   De esta forma, una celda tendrÃ¡ un valor asignado si y solo si dicho
;;; valor es el Ãºnico elemento del rango.

;;;   La siguiente variable global sirve enumerar las restricciones del puzle.

(defglobal ?*restricciones* = 0)

;;;   La siguiente funciÃ³n sirve para asignar de forma automÃ¡tica y Ãºnica
;;; identificadores a las restricciones del puzle.

(deffunction idRestriccion ()
  (bind ?*restricciones* (+ ?*restricciones* 1))
  ?*restricciones*)

;;;   Utilizaremos la siguiente plantilla para almacenar las restricciones del
;;; puzle. Cada restricciÃ³n tiene los siguientes campos:
;;; - id: Identificador Ãºnico de la restricciÃ³n
;;; - valor: Valor de la restricciÃ³n
;;; - casillas: Identificadores de las casillas que se ven afectadas por la
;;;   restricciÃ³n

(deftemplate restriccion
  (slot id
        (default-dynamic (idRestriccion)))
  (slot valor)
  (multislot casillas))

;;;============================================================================
;;; Estrategias de resolución
;;;============================================================================

;;;   El objetivo del trabajo consiste en implementar un conjunto de reglas
;;; CLIPS que resuelvan un Kakuro de forma deductiva, es decir, deduciendo el
;;; valor de una casilla a partir de reglas que analicen los posibles valores
;;; de las casillas relacionadas.

;;; Regla 1
;;; Eliminar los valores de las celdas mayores a los de las restricciones

(defrule elimina-mayores-a-restricciones
  (declare (salience 15))
  (restriccion (id ?) (valor ?r_v) (casillas $?r_ini ?r_c $?r_fin))
  ?h <- (celda (id ?r_c) (rango $?c_ini ?c_r&:(>= ?c_r ?r_v) $?c_fin))
  =>
  (modify ?h (rango $?c_ini $?c_fin))
  (printout t "Elimina valor imposible por restriccion" crlf))

;;; Regla 2
;;; Si una casilla solo tiene una restricción y es menor-igual que 9

(defrule casilla-unica
  ?h1 <- (restriccion (valor ?r_v&:(<= ?r_v 9)) (casillas ?r_c))
  ?h2 <- (celda (id ?r_c) (rango $?))
  =>
  (modify ?h2 (rango ?r_v))
  (printout t "Casilla con restriccion unica -> " ?r_c crlf))

;;; Regla 3
;;; Si es par y menor-igual que 18, no puede estar el valor/2 en ninguna casilla
(defrule elimina-mitad-si-par-menor-igual-18
  (declare (salience 10))
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2))
  (test (and (= (mod ?r_v 2) 0) (<= ?r_v 18)))
  ?h1 <- (celda (id ?r_c1) (rango $?c1_r_ini ?c1_v $?c1_r_fin))
  (test (= (/ ?r_v 2) ?c1_v))
  ?h2 <- (celda (id ?r_c2) (rango $?c2_r_ini ?c2_v $?c2_r_fin))
  (test (= (/ ?r_v 2) ?c2_v))
  =>
  (modify ?h1 (rango $?c1_r_ini $?c1_r_fin))
  (modify ?h2 (rango $?c2_r_ini $?c2_r_fin))
  (printout t "Elimina mitad si es par y <= 18 (" ?r_v ") -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Regla 4: eliminar los valores ya asignados en las filas
(defrule elimina-asignados-fila
  (declare (salience 10))
  (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  (celda (id ?r_c) (fila ?c2_f) (columna ?c2_c) (rango $?c2_r_ini ?c2_r&:(<= ?c2_r ?r_v) $?c2_r_fin))
  ?h3 <- (celda (id ?c3_id&~?r_c) (fila ?c2_f) (columna ?c3_c&~?c2_c) (rango $?c3_r_ini ?c2_r $?c3_r_fin))
  (test (and (= (length $?c2_r_ini) 0) (eq (length $?c2_r_fin) 0)))
  (test (or (> (length $?c3_r_ini) 0) (> (length $?c3_r_fin) 0)))
  (test (or (member ?c3_id $?r_c_ini) (member ?c3_id $?r_c_fin)))
  =>
  (modify ?h3 (rango $?c3_r_ini $?c3_r_fin))
  (printout t "Elimina valores ya asignados en fila -> " ?c3_id "(" ?c2_r ")" crlf)
)

;;; Regla 5: eliminar los valores ya asignados en las columnas
(defrule elimina-asignados-columna
  (declare (salience 10))
  (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  (celda (id ?r_c) (fila ?c2_f) (columna ?c2_c) (rango $?c2_r_ini ?c2_r&:(<= ?c2_r ?r_v) $?c2_r_fin))
  ?h3 <- (celda (id ?c3_id&~?r_c) (fila ?c3_f&~?c2_f) (columna ?c2_c) (rango $?c3_r_ini ?c2_r $?c3_r_fin))
  (test (and (= (length $?c2_r_ini) 0) (eq (length $?c2_r_fin) 0)))
  (test (or (> (length $?c3_r_ini) 0) (> (length $?c3_r_fin) 0)))
  (test (or (member ?c3_id $?r_c_ini) (member ?c3_id $?r_c_fin)))
  =>
  (modify ?h3 (rango $?c3_r_ini $?c3_r_fin))
  (printout t "Elimina valores ya asignados en columna -> " ?c3_id "(" ?c2_r ")" crlf)
)

;;; Regla 6: de los números comunes (restricción 2 a 2 de 17 y 16)
(defrule restriccion-2-a-2-de-17-16
  (restriccion (valor ?r1_v&:(= ?r1_v 17)) (casillas $?r1_c_ini ?r1_c $?r1_c_fin))
  (restriccion (valor ?r2_v&:(= ?r2_v 16)) (casillas $?r2_c_ini ?r2_c $?r2_c_fin))
  (test (= (+ (+ (length $?r1_c_ini) (length $?r1_c_fin)) 1) 2))
  (test (= (+ (+ (length $?r2_c_ini) (length $?r2_c_fin)) 1) 2))
  (test (eq ?r1_c ?r2_c))
  ?h1 <- (celda (id ?r1_c) (rango $?h1_ini ?r_c_v&:(eq ?r_c_v 9) $?h1_fin))
  (test (> (+ (+ (length $?h1_ini) (length $?h1_fin)) 1) 1))
  =>
  (modify ?h1 (rango 9))
  (printout t "Restriccion 2 a 2 de valor 17 y 16 -> " ?r1_c "(9)" crlf)
)

;;; Regla 7: completa una restriccion de 2 casillas en el que una esté resuelta
(defrule completa-2
  (celda (id ?c_c) (rango ?c_v))
  (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  (test (= (+ (+ (length $?r_c_ini) (length $?r_c_fin)) 1) 2))
  (test (member ?c_c (create$ $?r_c_ini ?r_c $?r_c_fin)))
  ?h1 <- (celda (id ?r_c&~?c_c) (rango $?h1_r))
  (test (> (length $?h1_r) 1))
  =>
  (bind ?result (- ?r_v ?c_v))
  (modify ?h1 (rango ?result))
  (printout t "Completa 2c -> " ?r_c " con valor " ?result crlf)
)

;;; Pares ocultos

;;; Regla 8:
(defrule par-asignado-fila
  ?h1 <- (celda (id ?c1_id) (fila ?c_f) (rango ?v1 ?v2))
  ?h2 <- (celda (id ?c2_id) (fila ?c_f) (rango ?v1 ?v2))
  (test (neq ?h1 ?h2))
  (restriccion (casillas $?r_c))
  (test (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)))
  ?h3 <- (celda (id ?c3_id) (fila ?c_f) (rango $?ini ?v&?v1|?v2 $?fin))
  (test (member ?c3_id $?r_c))
  (test (and (neq ?h1 ?h3) (neq ?h2 ?h3)))
  =>
  (modify ?h3 (rango $?ini $?fin))
  (printout t "Par oculto fila para valores (" ?v1 " " ?v2 ") en celda " ?c3_id " (quita " ?v ")" crlf)
)

;;; Regla 9:
(defrule par-asignado-columna
  ?h1 <- (celda (id ?c1_id) (columna ?c_c) (rango ?v1 ?v2))
  ?h2 <- (celda (id ?c2_id) (columna ?c_c) (rango ?v1 ?v2))
  (test (neq ?h1 ?h2))
  (restriccion (casillas $?r_c))
  (test (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)))
  ?h3 <- (celda (id ?c3_id) (columna ?c_c) (rango $?ini ?v&?v1|?v2 $?fin))
  (test (member ?c3_id $?r_c))
  (test (and (neq ?h1 ?h3) (neq ?h2 ?h3)))
  =>
  (modify ?h3 (rango $?ini $?fin))
  (printout t "Par oculto columna para valores (" ?v1 " " ?v2 ") en celda " ?c3_id " (quita " ?v ")" crlf)
)

;;; Trios ocultos

;;; Regla 10:
(defrule trio-asignado-fila
  ?h1 <- (celda (id ?c1_id) (fila ?c_f) (rango ?v1 ?v2 ?v3))
  ?h2 <- (celda (id ?c2_id) (fila ?c_f) (rango ?v1 ?v2 ?v3))
  ?h3 <- (celda (id ?c3_id) (fila ?c_f) (rango ?v1 ?v2 ?v3))
  (test (and (and (neq ?h1 ?h2) (neq ?h1 ?h3)) (neq ?h2 ?h3)))
  (restriccion (casillas $?r_c))
  (test (and (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)) (member ?c3_id $?r_c)))
  ?h4 <- (celda (id ?c4_id) (fila ?c_f) (rango $?ini ?v&?v1|?v2|?v3 $?fin))
  (test (member ?c4_id $?r_c))
  (test (and (and (neq ?h1 ?h4) (neq ?h2 ?h4)) (neq ?h3 ?h4)))
  =>
  (modify ?h4 (rango $?ini $?fin))
  (printout t "Trio oculto fila para valores (" ?v1 " " ?v2 " " ?v3 ") en celda " ?c4_id " (quita " ?v ")" crlf)
)

;;; Regla 11:
(defrule trio-asignado-columna
  ?h1 <- (celda (id ?c1_id) (columna ?c_c) (rango ?v1 ?v2 ?v3))
  ?h2 <- (celda (id ?c2_id) (columna ?c_c) (rango ?v1 ?v2 ?v3))
  ?h3 <- (celda (id ?c3_id) (columna ?c_c) (rango ?v1 ?v2 ?v3))
  (test (and (and (neq ?h1 ?h2) (neq ?h1 ?h3)) (neq ?h2 ?h3)))
  (restriccion (casillas $?r_c))
  (test (and (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)) (member ?c3_id $?r_c)))
  ?h4 <- (celda (id ?c4_id) (columna ?c_c) (rango $?ini ?v&?v1|?v2|?v3 $?fin))
  (test (member ?c4_id $?r_c))
  (test (and (and (neq ?h1 ?h4) (neq ?h2 ?h4)) (neq ?h3 ?h4)))
  =>
  (modify ?h4 (rango $?ini $?fin))
  (printout t "Trio oculto columna para valores (" ?v1 " " ?v2 " " ?v3 ") en celda " ?c4_id " (quita " ?v ")" crlf)
)

; ;;; Cuadriples ocultos
;
; ;;; Regla 12:
; (defrule cuadruple-asignado-fila
;   ?h1 <- (celda (id ?c1_id) (fila ?c_f) (rango ?v1 ?v2 ?v3 ?v4))
;   ?h2 <- (celda (id ?c2_id) (fila ?c_f) (rango ?v1 ?v2 ?v3 ?v4))
;   (test (neq ?h1 ?h2))
;   (restriccion (casillas $?r_c))
;   (test (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)))
;   ?h3 <- (celda (id ?c3_id) (fila ?c_f) (rango $?ini ?v&?v1|?v2|?v3|?v4 $?fin))
;   (test (member ?c3_id $?r_c))
;   (test (and (neq ?h1 ?h3) (neq ?h2 ?h3)))
;   =>
;   (modify ?h3 (rango $?ini $?fin))
;   (printout t "Cuadruple oculto fila para valores (" ?v1 " " ?v2 " " ?v3 " " ?v4 ") en celda " ?c3_id " (quita " ?v ")" crlf)
; )
;
; ;;; Regla 13:
; (defrule cuadruple-asignado-columna
;   ?h1 <- (celda (id ?c1_id) (columna ?c_c) (rango ?v1 ?v2 ?v3 ?v4))
;   ?h2 <- (celda (id ?c2_id) (columna ?c_c) (rango ?v1 ?v2 ?v3 ?v4))
;   (test (neq ?h1 ?h2))
;   (restriccion (casillas $?r_c))
;   (test (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)))
;   ?h3 <- (celda (id ?c3_id) (columna ?c_c) (rango $?ini ?v&?v1|?v2|?v3|?v4 $?fin))
;   (test (member ?c3_id $?r_c))
;   (test (and (neq ?h1 ?h3) (neq ?h2 ?h3)))
;   =>
;   (modify ?h3 (rango $?ini $?fin))
;   (printout t "Cuadruple oculto columna para valores (" ?v1 " " ?v2 " " ?v3 " " ?v4 ") en celda " ?c3_id " (quita " ?v ")" crlf)
; )

;;; Regla 14
(defrule max-valores-2
  (restriccion (valor ?r_v) (casillas ?v1 ?v2))
  ?h1 <- (celda (id ?v1) (rango $?c1_ini ?c1_v))
  (test (> (+ (length $?c1_ini) 1) 1))
  ?h2 <- (celda (id ?v2) (rango $?c2_ini ?c2_v&~?c1_v))
  (test (> (+ (length $?c2_ini) 1) 1))
  (test (= (+ ?c1_v ?c2_v) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (printout t "Valores maximos 2c -> " ?v1 "(" ?c1_v "), " ?v2 "(" ?c2_v ")" crlf)
)

;;; Regla 15
(defrule max-valores-3
  (restriccion (valor ?r_v) (casillas ?v1 ?v2 ?v3))
  ?h1 <- (celda (id ?v1) (rango $?c1_ini ?c1_v))
  (test (> (+ (length $?c1_ini) 1) 1))
  ?h2 <- (celda (id ?v2) (rango $?c2_ini ?c2_v))
  (test (> (+ (length $?c2_ini) 1) 1))
  ?h3 <- (celda (id ?v3) (rango $?c3_ini ?c3_v))
  (test (> (+ (length $?c3_ini) 1) 1))
  (test (= (+ ?c1_v (+ ?c2_v ?c3_v)) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (printout t "Valores maximos 3c -> " ?v1 "(" ?c1_v "), " ?v2 "(" ?c2_v "), " ?v3 "(" ?c3_v ")" crlf)
)

;;; Regla 16
(defrule max-valores-4
  (restriccion (valor ?r_v) (casillas ?v1 ?v2 ?v3 ?v4))
  ?h1 <- (celda (id ?v1) (rango $?c1_ini ?c1_v))
  (test (> (+ (length $?c1_ini) 1) 1))
  ?h2 <- (celda (id ?v2) (rango $?c2_ini ?c2_v))
  (test (> (+ (length $?c2_ini) 1) 1))
  ?h3 <- (celda (id ?v3) (rango $?c3_ini ?c3_v))
  (test (> (+ (length $?c3_ini) 1) 1))
  ?h4 <- (celda (id ?v4) (rango $?c4_ini ?c4_v))
  (test (> (+ (length $?c4_ini) 1) 1))
  (test (= (+ ?c1_v (+ ?c2_v (+ ?c3_v ?c4_v))) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (modify ?h3 (rango ?c4_v))
  (printout t "Valores maximos 4c -> " ?v1 "(" ?c1_v "), " ?v2 "(" ?c2_v "), " ?v3 "(" ?c3_v "), " ?v4 "(" ?c4_v ")" crlf)
)

;;; Regla 17
(defrule min-valores-2
  (restriccion (valor ?r_v) (casillas ?v1 ?v2))
  ?h1 <- (celda (id ?v1) (rango ?c1_v $?c1_fin))
  (test (> (+ (length $?c1_fin) 1) 1))
  ?h2 <- (celda (id ?v2) (rango ?c2_v&~?c1_v $?c2_fin))
  (test (> (+ (length $?c2_fin) 1) 1))
  (test (= (+ ?c1_v ?c2_v) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (printout t "Valores minimos 2c -> " ?v1 "(" ?c1_v "), " ?v2 "(" ?c2_v ")" crlf)
)

;;; Regla 18
(defrule min-valores-3
  (restriccion (valor ?r_v) (casillas ?v1 ?v2 ?v3))
  ?h1 <- (celda (id ?v1) (rango ?c1_v $?c1_fin))
  (test (> (+ (length $?c1_fin) 1) 1))
  ?h2 <- (celda (id ?v2) (rango ?c2_v&~?c1_v $?c2_fin))
  (test (> (+ (length $?c2_fin) 1) 1))
  ?h3 <- (celda (id ?v3) (rango ?c3_v&~?c1_v&~?c2_v $?c3_fin))
  (test (> (+ (length $?c3_fin) 1) 1))
  (test (= (+ ?c1_v (+ ?c2_v ?c3_v)) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (printout t "Valores minimos 3c -> " ?v1 "(" ?c1_v "), " ?v2 "(" ?c2_v ")," ?v3 "(" ?c3_v ")" crlf)
)

;;; Regla 19
(defrule min-valores-4
  (restriccion (valor ?r_v) (casillas ?v1 ?v2 ?v3 ?v4))
  ?h1 <- (celda (id ?v1) (rango ?c1_v $?c1_fin))
  (test (> (+ (length $?c1_fin) 1) 1))
  ?h2 <- (celda (id ?v2) (rango ?c2_v $?c2_fin))
  (test (> (+ (length $?c2_fin) 1) 1))
  ?h3 <- (celda (id ?v3) (rango ?c3_v $?c3_fin))
  (test (> (+ (length $?c3_fin) 1) 1))
  ?h4 <- (celda (id ?v4) (rango ?c4_v $?c4_fin))
  (test (> (+ (length $?c4_fin) 1) 1))
  (test (= (+ ?c1_v (+ ?c2_v (+ ?c3_v ?c4_v))) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (modify ?h3 (rango ?c4_v))
  (printout t "Valores minimos 4c -> " ?v1 "(" ?c1_v "), " ?v2 "(" ?c2_v "), " ?v3 "(" ?c3_v "), " ?v4 "(" ?c4_v ")" crlf)
)

;;; Regla 20
(defrule detecta-cuadro-con-1-extra
  (restriccion (valor ?r1_v) (casillas ?r1_c1 ?r1_c2))
  (restriccion (valor ?r2_v) (casillas ?r2_c1 ?r2_c2))
  (restriccion (valor ?r3_v) (casillas ?r1_c1 ?r2_c1))
  (restriccion (valor ?r4_v) (casillas ?r1_c2 ?r2_c2 ?r4_c3))
  ?h1 <- (celda (id ?r4_c3) (rango $?c_r))
  (test (> (length $?c_r) 1))
  =>
  (bind ?result (abs (- (- (+ ?r1_v ?r2_v) ?r3_v) ?r4_v)))
  (modify ?h1 (rango ?result))
  (printout t "Detecta 2x2 con 1 extra -> " ?r4_c3 "(" ?result ")"  crlf)
)

;;; Regla 21
(defrule detecta-cuadro-con-1-extra-2
  (restriccion (valor ?r1_v) (casillas ?r1_c1 ?r1_c2))
  (restriccion (valor ?r2_v) (casillas ?r2_c1 ?r2_c2))
  (restriccion (valor ?r3_v) (casillas ?r1_c2 ?r2_c2))
  (restriccion (valor ?r4_v) (casillas ?r1_c1 ?r2_c1 ?r4_c3))
  ?h1 <- (celda (id ?r4_c3) (rango $?c_r))
  (test (> (length $?c_r) 1))
  =>
  (bind ?result (abs (- (- (+ ?r1_v ?r2_v) ?r3_v) ?r4_v)))
  (modify ?h1 (rango ?result))
  (printout t "Detecta 2x2 con 1 extra -> " ?r4_c3 "(" ?result ")"  crlf)
)

;;; Regla 22
(defrule detecta-cuadro-con-1-extra-3
  (restriccion (valor ?r1_v) (casillas ?r1_c1 ?r1_c2))
  (restriccion (valor ?r2_v) (casillas ?r2_c1 ?r2_c2))
  (restriccion (valor ?r3_v) (casillas ?r1_c1 ?r2_c1))
  (restriccion (valor ?r4_v) (casillas ?r4_c3 ?r1_c2 ?r2_c2))
  ?h1 <- (celda (id ?r4_c3) (rango $?c_r))
  (test (> (length $?c_r) 1))
  =>
  (bind ?result (abs (- (- (+ ?r1_v ?r2_v) ?r3_v) ?r4_v)))
  (modify ?h1 (rango ?result))
  (printout t "Detecta 2x2 con 1 extra -> " ?r4_c3 "(" ?result ")"  crlf)
)

;;; Regla 23
(defrule detecta-cuadro-con-1-extra-4
  (restriccion (valor ?r1_v) (casillas ?r1_c1 ?r1_c2))
  (restriccion (valor ?r2_v) (casillas ?r2_c1 ?r2_c2))
  (restriccion (valor ?r3_v) (casillas ?r1_c2 ?r2_c2))
  (restriccion (valor ?r4_v) (casillas ?r4_c3 ?r1_c1 ?r2_c1))
  ?h1 <- (celda (id ?r4_c3) (rango $?c_r))
  (test (> (length $?c_r) 1))
  =>
  (bind ?result (abs (- (- (+ ?r1_v ?r2_v) ?r3_v) ?r4_v)))
  (modify ?h1 (rango ?result))
  (printout t "Detecta 2x2 con 1 extra -> " ?r4_c3 "(" ?result ")"  crlf)
)

;;; Regla 24
(defrule completa-3-1
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  ?h1 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (> (length $?c_r3) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 3c -> " ?r_c3 " con valor " ?result crlf)
)

;;; Regla 25
(defrule completa-3-2
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r3)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 3c -> " ?r_c2 " con valor " ?result crlf)
)

;;; Regla 26
(defrule completa-3-3
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r2 ?c_r3)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 3c -> " ?r_c1 " con valor " ?result crlf)
)

;;; Regla 27
(defrule completa-4-1
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (> (length $?c_r4) 1))
  =>
  (bind ?result (- ?r_v (+ (+ ?c_r1 ?c_r2) ?c_r3)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 4c -> " ?r_c4 " con valor " ?result crlf)
)

;;; Regla 28
(defrule completa-4-2
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (> (length $?c_r3) 1))
  =>
  (bind ?result (- ?r_v (+ (+ ?c_r1 ?c_r2) ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 4c -> " ?r_c3 " con valor " ?result crlf)
)

;;; Regla 29
(defrule completa-4-3
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c4) (rango ?c_r4))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 1))
  =>
  (bind ?result (- ?r_v (+ (+ ?c_r1 ?c_r4) ?c_r3)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 4c -> " ?r_c2 " con valor " ?result crlf)
)

;;; Regla 30
(defrule completa-4-4
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  (celda (id ?r_c4) (rango ?c_r4))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 1))
  =>
  (bind ?result (- ?r_v (+ (+ ?c_r4 ?c_r2) ?c_r3)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 4c -> " ?r_c1 " con valor " ?result crlf)
)

;;; Regla 31
(defrule completa-5-1
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c5) (rango $?c_r5))
  (test (> (length $?c_r5) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c5 " con valor " ?result crlf)
)

;;; Regla 32
(defrule completa-5-2
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c5) (rango ?c_r5))
  ?h1 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (> (length $?c_r4) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c4 " con valor " ?result crlf)
)

;;; Regla 33
(defrule completa-5-3
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c5) (rango ?c_r5))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (> (length $?c_r3) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ ?c_r1 ?c_r2) ?c_r5) ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c3 " con valor " ?result crlf)
)

;;; Regla 34
(defrule completa-5-4
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c5) (rango ?c_r5))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ ?c_r1 ?c_r5) ?c_r3) ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c2 " con valor " ?result crlf)
)

;;; Regla 35
(defrule completa-5-5
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c5) (rango ?c_r5))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ ?c_r5 ?c_r2) ?c_r3) ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c1 " con valor " ?result crlf)
)

;;; Regla 36
(defrule completa-6-1
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5 ?r_c6))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  (celda (id ?r_c5) (rango ?c_r5))
  ?h1 <- (celda (id ?r_c6) (rango $?c_r6))
  (test (> (length $?c_r6) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r4) ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c6 " con valor " ?result crlf)
)

;;; Regla 37
(defrule completa-6-2
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5 ?r_c6))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  (celda (id ?r_c6) (rango ?c_r6))
  ?h1 <- (celda (id ?r_c5) (rango $?c_r5))
  (test (> (length $?c_r5) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r4) ?c_r6)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c5 " con valor " ?result crlf)
)

;;; Regla 38
(defrule completa-6-3
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5 ?r_c6))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c6) (rango ?c_r6))
  (celda (id ?r_c5) (rango ?c_r5))
  ?h1 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (> (length $?c_r4) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r6) ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c4 " con valor " ?result crlf)
)

;;; Regla 39
(defrule completa-6-4
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5 ?r_c6))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c6) (rango ?c_r6))
  (celda (id ?r_c4) (rango ?c_r4))
  (celda (id ?r_c5) (rango ?c_r5))
  ?h1 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (> (length $?c_r3) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r2) ?c_r6) ?c_r4) ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c3 " con valor " ?result crlf)
)

;;; Regla 40
(defrule completa-6-5
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5 ?r_c6))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c6) (rango ?c_r6))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  (celda (id ?r_c5) (rango ?c_r5))
  ?h1 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r6) ?c_r3) ?c_r4) ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c2 " con valor " ?result crlf)
)

;;; Regla 41
(defrule completa-6-6
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5 ?r_c6))
  (celda (id ?r_c6) (rango ?c_r6))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  (celda (id ?r_c5) (rango ?c_r5))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 1))
  =>
  (bind ?result (- ?r_v (+ (+ (+ (+ ?c_r6 ?c_r2) ?c_r3) ?c_r4) ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c1 " con valor " ?result crlf)
)

;;; Sumas únicas de 2 casillas

;;; Regla 42
(defrule suma-unica-2c-3
  (declare (salience 10))
  (restriccion (valor 3) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango 1 2 $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango 1 2 $?c_r2))
  (test (or (> (length $?c_r1) 0)
            (> (length $?c_r2) 0)))
  =>
  (modify ?h1 (rango 1 2))
  (modify ?h2 (rango 1 2))
  (printout t "Suma unica 2c 3 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Regla 43
(defrule suma-unica-2c-4
  (declare (salience 10))
  (restriccion (valor 4) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango 1 $?c_r1_m 3 $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango 1 $?c_r2_m 3 $?c_r2))
  (test (or (> (length (create$ $?c_r2 $?c_r2_m)) 0)
            (> (length (create$ $?c_r1 $?c_r1_m)) 0)))
  =>
  (modify ?h1 (rango 1 3))
  (modify ?h2 (rango 1 3))
  (printout t "Suma unica 2c 4 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Regla 44
(defrule suma-unica-2c-16
  (declare (salience 10))
  (restriccion (valor 16) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1 7 $?c_r1_m 9))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2 7 $?c_r2_m 9))
  (test (or (> (length (create$ $?c_r2 $?c_r2_m)) 0)
            (> (length (create$ $?c_r1 $?c_r1_m)) 0)))
  =>
  (modify ?h1 (rango 7 9))
  (modify ?h2 (rango 7 9))
  (printout t "Suma unica 2c 16 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Regla 45
(defrule suma-unica-2c-17
  (declare (salience 10))
  (restriccion (valor 17) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1 8 9))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2 8 9))
  (test (or (> (length $?c_r2) 0) (> (length $?c_r1) 0)))
  =>
  (modify ?h1 (rango 8 9))
  (modify ?h2 (rango 8 9))
  (printout t "Suma unica 2c 17 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Regla 46
(defrule busca-candidato-unico-2c
  (declare (salience -5))
  (restriccion (valor ?r_v&:(<= ?r_v 18)) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 1))
  (test (neq ?r_c1 ?r_c2))
  =>
  (bind ?c_candidate1 0)
  (bind ?c_candidate2 0)
  (bind ?results 0)
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (loop-for-count (?j 1 (length $?c_r2)) do
      (bind ?b (nth$ ?j $?c_r2))
      (if (= ?r_v (+ ?a ?b))
        then (bind ?results (+ ?results +1))
             (bind ?c_candidate1 ?a)
             (bind ?c_candidate2 ?b)
      )
    )
  )
  (if (= ?results 1)
    then (modify ?h1 (rango ?c_candidate1))
         (modify ?h2 (rango ?c_candidate2))
         (printout t "Encuentra candidado unico 2c -> " ?r_c1 "(" ?c_candidate1 "), " ?r_c2 "(" ?c_candidate2 ")" crlf)
  )
)

;;; Regla 47
(defrule busca-candidato-unico-3c-1 ;1 resuelta - 2 no
  (declare (salience -5))
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  (celda (id ?r_c1) (rango ?c_r1))
  ?h1 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h2 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (> (length $?c_r2) 1))
  (test (> (length $?c_r3) 1))
  =>
  (bind ?r_v (- ?r_v ?c_r1))
  (bind ?c_candidate1 0)
  (bind ?c_candidate2 0)
  (bind ?results 0)
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (loop-for-count (?j 1 (length $?c_r3)) do
      (bind ?b (nth$ ?j $?c_r3))
      (if (and (= ?r_v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?results (+ ?results +1))
             (bind ?c_candidate1 ?a)
             (bind ?c_candidate2 ?b)
      )
    )
  )
  (if (= ?results 1)
    then (modify ?h1 (rango ?c_candidate1))
         (modify ?h2 (rango ?c_candidate2))
         (printout t "Encuentra candidado unico 3c -> " ?r_c2 "(" ?c_candidate1 "), " ?r_c3 "(" ?c_candidate2 ")" crlf)
  )
)

(defrule busca-candidado-unico-3c-2 ;1 resuelta - 2 no
  (declare (salience -5))
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  ?h2 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (> (length $?c_r1) 1))
  (test (> (length $?c_r3) 1))
  =>
  (bind ?r_v (- ?r_v ?c_r2))
  (bind ?c_candidate1 0)
  (bind ?c_candidate2 0)
  (bind ?results 0)
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (loop-for-count (?j 1 (length $?c_r3)) do
      (bind ?b (nth$ ?j $?c_r3))
      (if (and (= ?r_v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?results (+ ?results +1))
             (bind ?c_candidate1 ?a)
             (bind ?c_candidate2 ?b)
      )
    )
  )
  (if (= ?results 1)
    then (modify ?h1 (rango ?c_candidate1))
         (modify ?h2 (rango ?c_candidate2))
         (printout t "Encuentra candidado unico 3c -> " ?r_c1 "(" ?c_candidate1 "), " ?r_c3 "(" ?c_candidate2 ")" crlf)
  )
)

(defrule busca-candidado-unico-3c-3 ;1 resuelta - 2 no
  (declare (salience -5))
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (test (> (length $?c_r1) 1))
  (test (> (length $?c_r2) 1))
  =>
  (bind ?r_v (- ?r_v ?c_r3))
  (bind ?c_candidate1 0)
  (bind ?c_candidate2 0)
  (bind ?results 0)
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (loop-for-count (?j 1 (length $?c_r2)) do
      (bind ?b (nth$ ?j $?c_r2))
      (if (and (= ?r_v (+ ?a ?b)) (neq ?a ?b))
        then
             (bind ?results (+ ?results +1))
             (bind ?c_candidate1 ?a)
             (bind ?c_candidate2 ?b)
      )
    )
  )
  (if (= ?results 1)
    then (modify ?h1 (rango ?c_candidate1))
         (modify ?h2 (rango ?c_candidate2))
  )
)

;;;============================================================================
;;; Reglas para imprimir el resultado
;;;============================================================================

;;;   Las siguientes reglas permiten visualizar el estado del puzle, una vez
;;; aplicadas todas las reglas que implementan las estrategias de resoluciÃ³n.
;;; La prioridad de estas reglas es -10 para que sean las Ãºltimas en
;;; aplicarse.

;;;   Para las casillas del tablero con un Ãºnico valor en su rango se indica
;;; dicho valor, para las casillas del tablero en las que no se haya podido
;;; deducir el valor se indica el sÃ­mbolo '?'. El resto de las casillas hasta
;;; completar la cuadrÃ­cula 9x9 se dejan en blanco.

(defrule imprime-solucion
  (declare (salience -10))
  =>
  (printout t "+---------+" crlf "|")
  (assert (imprime 1 1)))

(defrule imprime-celda-1
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (celda (fila ?i) (columna ?j) (rango $?v))
  =>
  (retract ?h)
  (if (= (length$ $?v) 1)
      then (printout t (nth$ 1 $?v))
    else (printout t "?"))
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

(defrule imprime-celda-2
  (declare (salience -10))
  ?h <- (imprime ?i ?j&:(<= (* ?i ?j) 81))
  (not (celda (fila ?i) (columna ?j) (rango $?v)))
  =>
  (retract ?h)
  (printout t " ")
  (if (= ?j 9)
      then (printout t "|" crlf))
  (if (and (= ?i 9) (= ?j 9))
      then (printout t "+---------+" crlf))
  (if (and (= ?j 9) (not (= ?i 9)))
      then (printout t "|")
           (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

;;;============================================================================
;;; Funcionalidad para leer los puzles del fichero de ejemplos
;;;============================================================================

;;;   Esta funciÃ³n crea una lista de identificadores de casillas en horizontal.

(deffunction crea-casillas-horizontal (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat ?f (+ ?c ?i))))))
  ?datos)

;;;   Esta funciÃ³n construye los hechos que representan las restricciones de
;;; una lÃ­nea horizontal del Kakuro.

(deffunction procesa-restricciones-fila (?f $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?c ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?c))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-horizontal ?f ?c (- ?i ?c)))))))
  TRUE)

;;;   Esta funciÃ³n crea una lista de identificadores de casillas en vertical.

(deffunction crea-casillas-vertical (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat (+ ?f ?i) ?c)))))
  ?datos)

;;;   Esta funciÃ³n construye los hechos que representan las restricciones de
;;; una lÃ­nea horizontal del Kakuro.

(deffunction procesa-restricciones-columna (?c $?linea)
  (bind ?i 1)
  (bind ?d (nth$ ?i $?linea))
  (while (< ?i 9)
    (bind ?v 0)
    (while (and (<= ?i 9) (not (numberp ?d)))
      (bind ?i (+ ?i 1))
      (bind ?d (nth$ ?i $?linea)))
    (bind ?f ?i)
    (while (and (<= ?i 9) (numberp ?d))
      (bind ?i (+ ?i 1))
      (bind ?v (+ ?v ?d))
      (bind ?d (nth$ ?i $?linea)))
    (if (< 0 (- ?i ?f))
        then (assert (restriccion
                      (valor ?v)
                      (casillas
                       (crea-casillas-vertical ?f ?c (- ?i ?f)))))))
  TRUE)

;;;   Esta funciÃ³n construye todos los hechos que representan las restricciones
;;; de un Kakuro dado en el formato utilizado en el fichero de ejemplos.

(deffunction procesa-restricciones-ejemplo (?datos)
  (loop-for-count
   (?i 1 9)
   (bind $?linea (create$))
   (loop-for-count
    (?j 2 10)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-fila ?i ?linea))
  (loop-for-count
   (?j 2 10)
   (bind $?linea (create$))
   (loop-for-count
    (?i 1 9)
    (bind ?linea (insert$ ?linea 10
                          (eval (sub-string (+ (* 10 ?i) ?j)
                                            (+ (* 10 ?i) ?j) ?datos)))))
   (procesa-restricciones-columna (- ?j 1) ?linea))
  TRUE)

;;;   Esta funciÃ³n localiza el Kakuro que se quiere resolver en el fichero de
;;; ejemplos.

(deffunction lee-kakuro (?n)
  (open "ejemplos.txt" data "r")
  (loop-for-count (?i 1 (- ?n 1))
                  (readline data))
  (bind ?datos (readline data))
  (procesa-restricciones-ejemplo ?datos)
  (close data))

;;;   Esta regla pregunta al usuario que nÃºmero de Kakuro del fichero de
;;; ejemplos se quiere resolver y genera los hechos que representan las
;;; restricciones asociadas.

(defrule kakuro-numero
  (declare (salience 100))
  =>
  (printout t "Que problema quieres resolver (1-50)? : ")
  (lee-kakuro (read)))

;;;   Esta regla construye las celdas que aparecen en alguna de las
;;; restricciones del Kakuro que se quiere resolver.

(defrule crea-celdas-restricciones
  (declare (salience 100))
  (restriccion (casillas $? ?id $?))
  (not (celda (id ?id)))
  =>
  (assert (celda (id ?id) (fila (div ?id 10)) (columna (mod ?id 10)))))

;;;============================================================================
