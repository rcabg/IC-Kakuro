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
  (declare (salience 10))
  (restriccion (id ?) (valor ?r_v) (casillas $?r_ini ?r_c $?r_fin))
  ?h <- (celda (id ?r_c) (rango $?c_ini ?c_r&:(>= ?c_r ?r_v) $?c_fin))
  =>
  (modify ?h (rango $?c_ini $?c_fin))
  (printout t "Se activa regla 1" crlf))


;;; Si una casilla solo tiene una restricción y es menor-igual que 9

;;; Regla 2
(defrule casilla-unica
  ?h1 <- (restriccion (valor ?r_v&:(<= ?r_v 9)) (casillas ?r_c))
  ?h2 <- (celda (id ?r_c) (rango $?))
  =>
  (modify ?h2 (rango ?r_v))
  (printout t "Se activa regla 2" crlf))

;;; Regla 3
;;; Si es par y menor-igual que 18, no puede estar el valor/2 en ninguna casilla
(defrule elimina-mitad-si-par-menor-igual-18
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2))
  (test (and (= (mod ?r_v 2) 0) (<= ?r_v 18)))
  ?h1 <- (celda (id ?r_c1) (rango $?c1_r_ini ?r_v&:(= (div ?r_v 2)) $?c1_r_fin))
  ?h2 <- (celda (id ?r_c2) (rango $?c2_r_ini ?r_v&:(= (div ?r_v 2)) $?c2_r_fin))
  =>
  (modify ?h1 (rango $?c1_r_ini $?c1_r_fin))
  (modify ?h2 (rango $?c2_r_ini $?c2_r_fin))
  (printout t "Elimina mitad si es par y <= 18" crlf)
)

;;; Regla 4: eliminar los valores ya asignados en las filas
(defrule eliminar-asignados-fila
  ?h1 <- (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  ?h2 <- (celda (id ?c2_id&:(= ?c2_id ?r_c)) (fila ?c2_f) (columna ?c2_c) (rango $?c2_r_ini ?c2_r&:(<= ?c2_r ?r_v) $?c2_r_fin))
  ?h3 <- (celda (id ?c3_id&~?c2_id) (fila ?c3_f&:(= ?c3_f ?c2_f)) (columna ?c3_c&~?c2_c) (rango $?c3_r_ini ?c3_r&:(= ?c3_r ?c2_r) $?c3_r_fin))
  (test (and (= (length $?c2_r_ini) 0) (eq (length $?c2_r_fin) 0)))
  (test (or (> (length $?c3_r_ini) 0) (> (length $?c3_r_fin) 0)))
  (test (or (member ?c3_id $?r_c_ini) (member ?c3_id $?r_c_fin)))
  =>
  (modify ?h3 (rango $?c3_r_ini $?c3_r_fin))
  (printout t "Se activa regla 4" crlf)
)

;;; Regla 5: eliminar los valores ya asignados en las columnas
(defrule eliminar-asignados-columna
  ?h1 <- (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  ?h2 <- (celda (id ?c2_id&:(= ?c2_id ?r_c)) (fila ?c2_f) (columna ?c2_c) (rango $?c2_r_ini ?c2_r&:(<= ?c2_r ?r_v) $?c2_r_fin))
  ?h3 <- (celda (id ?c3_id&~?c2_id) (fila ?c3_f&~?c2_f) (columna ?c3_c&:(= ?c3_c ?c2_c)) (rango $?c3_r_ini ?c3_r&:(= ?c3_r ?c2_r) $?c3_r_fin))
  (test (and (= (length $?c2_r_ini) 0) (eq (length $?c2_r_fin) 0)))
  (test (or (> (length $?c3_r_ini) 0) (> (length $?c3_r_fin) 0)))
  (test (or (member ?c3_id $?r_c_ini) (member ?c3_id $?r_c_fin)))
  =>
  (modify ?h3 (rango $?c3_r_ini $?c3_r_fin))
  (printout t "Se activa regla 5" crlf)
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
  (printout t "Se activa regla 6" crlf)
)

;(defrule restriccion-2-a-2-de-17-16-2
;  (celda (id ?c_c) (rango ?c_v&:(= ?c_v 9)))
;  (restriccion (valor ?r1_v&:(= ?r1_v 17)) (casillas $?r1_c_ini ?r1_c $?r1_c_fin))
;  (test (= (+ (+ (length $?r1_c_ini) (length $?r1_c_fin)) 1) 2))
;  (test (member ?c_c (create$ $?r1_c_ini ?r1_c $?r1_c_fin)))
;  (restriccion (valor ?r2_v&:(= ?r2_v 16)) (casillas $?r2_c_ini ?r2_c $?r2_c_fin))
;  (test (= (+ (+ (length $?r2_c_ini) (length $?r2_c_fin)) 1) 2))
;  (test (member ?c_c (create$ $?r2_c_ini ?r2_c $?r2_c_fin)))
;  ?h1 <- (celda (id ?r1_c&~?c_c) (rango $?h1_ini ?r1_c_v&:(eq ?r1_c_v 8) $?h1_fin))
;  (test (> (+ (+ (length $?h1_ini) (length $?h1_fin)) 1) 1))
;  ?h2 <- (celda (id ?r2_c&~?c_c) (rango $?h2_ini ?r2_c_v&:(eq ?r2_c_v 7) $?h2_fin))
;  (test (> (+ (+ (length $?h2_ini) (length $?h2_fin)) 1) 1))
;  =>
;  (modify ?h1 (rango 8))
;  (modify ?h2 (rango 7))
;  (printout t "Se activa regla 5" crlf)
;)

;;; Regla 7: completa una restriccion de 2 casillas en el que una esté resuelta
(defrule completa-2
  (celda (id ?c_c) (rango ?c_v))
  (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  (test (= (+ (+ (length $?r_c_ini) (length $?r_c_fin)) 1) 2))
  (test (member ?c_c (create$ $?r_c_ini ?r_c $?r_c_fin)))
  ?h1 <- (celda (id ?r_c&~?c_c) (rango $?h1_r))
  (test (> (length $?h1_r) 1))
  =>
  (modify ?h1 (rango (- ?r_v ?c_v)))
  (printout t "Se activa regla 7" crlf)
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
  (printout t "Se activa regla 8" crlf)
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
  (printout t "Se activa regla 9" crlf)
)

;;; Trios ocultos

;;; Regla 10:
(defrule trio-asignado-fila
  ?h1 <- (celda (id ?c1_id) (fila ?c_f) (rango ?v1 ?v2 ?v3))
  ?h2 <- (celda (id ?c2_id) (fila ?c_f) (rango ?v1 ?v2 ?v3))
  (test (neq ?h1 ?h2))
  (restriccion (casillas $?r_c))
  (test (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)))
  ?h3 <- (celda (id ?c3_id) (fila ?c_f) (rango $?ini ?v&?v1|?v2|?v3 $?fin))
  (test (member ?c3_id $?r_c))
  (test (and (neq ?h1 ?h3) (neq ?h2 ?h3)))
  =>
  (modify ?h3 (rango $?ini $?fin))
  (printout t "Se activa regla 10" crlf)
)

;;; Regla 11:
(defrule trio-asignado-columna
  ?h1 <- (celda (id ?c1_id) (columna ?c_c) (rango ?v1 ?v2 ?v3))
  ?h2 <- (celda (id ?c2_id) (columna ?c_c) (rango ?v1 ?v2 ?v3))
  (test (neq ?h1 ?h2))
  (restriccion (casillas $?r_c))
  (test (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)))
  ?h3 <- (celda (id ?c3_id) (columna ?c_c) (rango $?ini ?v&?v1|?v2|?v3 $?fin))
  (test (member ?c3_id $?r_c))
  (test (and (neq ?h1 ?h3) (neq ?h2 ?h3)))
  =>
  (modify ?h3 (rango $?ini $?fin))
  (printout t "Se activa regla 11" crlf)
)

;;; Cuadriples ocultos

;;; Regla 12:
(defrule cuadruple-asignado-fila
  ?h1 <- (celda (id ?c1_id) (fila ?c_f) (rango ?v1 ?v2 ?v3 ?v4))
  ?h2 <- (celda (id ?c2_id) (fila ?c_f) (rango ?v1 ?v2 ?v3 ?v4))
  (test (neq ?h1 ?h2))
  (restriccion (casillas $?r_c))
  (test (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)))
  ?h3 <- (celda (id ?c3_id) (fila ?c_f) (rango $?ini ?v&?v1|?v2|?v3|?v4 $?fin))
  (test (member ?c3_id $?r_c))
  (test (and (neq ?h1 ?h3) (neq ?h2 ?h3)))
  =>
  (modify ?h3 (rango $?ini $?fin))
  (printout t "Se activa regla 12" crlf)
)

;;; Regla 13:
(defrule cuadruple-asignado-columna
  ?h1 <- (celda (id ?c1_id) (columna ?c_c) (rango ?v1 ?v2 ?v3 ?v4))
  ?h2 <- (celda (id ?c2_id) (columna ?c_c) (rango ?v1 ?v2 ?v3 ?v4))
  (test (neq ?h1 ?h2))
  (restriccion (casillas $?r_c))
  (test (and (member ?c1_id $?r_c) (member ?c2_id $?r_c)))
  ?h3 <- (celda (id ?c3_id) (columna ?c_c) (rango $?ini ?v&?v1|?v2|?v3|?v4 $?fin))
  (test (member ?c3_id $?r_c))
  (test (and (neq ?h1 ?h3) (neq ?h2 ?h3)))
  =>
  (modify ?h3 (rango $?ini $?fin))
  (printout t "Se activa regla 13" crlf)
)

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
  (printout t "Se activa regla 14" crlf)
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
  (printout t "Se activa regla 15" crlf)
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
  (printout t "Se activa regla 16" crlf)
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
  (printout t "Se activa regla 17" crlf)
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
  (printout t "Se activa regla 18" crlf)
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
  (printout t "Se activa regla 19" crlf)
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
  (modify ?h1 (rango (abs (- (- (+ ?r1_v ?r2_v) ?r3_v) ?r4_v))))
  (printout t "Se activa regla 20" crlf)
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
  (modify ?h1 (rango (abs (- (- (+ ?r1_v ?r2_v) ?r3_v) ?r4_v))))
  (printout t "Se activa regla 21" crlf)
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
  (modify ?h1 (rango (abs (- (- (+ ?r1_v ?r2_v) ?r3_v) ?r4_v))))
  (printout t "Se activa regla 22" crlf)
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
  (modify ?h1 (rango (abs (- (- (+ ?r1_v ?r2_v) ?r3_v) ?r4_v))))
  (printout t "Se activa regla 23" crlf)
)

;;; Regla 24
(defrule completa-3-1
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  ?h1 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (> (length $?c_r3) 1))
  =>
  (modify ?h1 (rango (- ?r_v (+ ?c_r1 ?c_r2))))
  (printout t "Se activa regla 24" crlf)
)

;;; Regla 25
(defrule completa-3-2
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 1))
  =>
  (modify ?h1 (rango (- ?r_v (+ ?c_r1 ?c_r3))))
  (printout t "Se activa regla 25" crlf)
)

;;; Regla 26
(defrule completa-3-3
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 1))
  =>
  (modify ?h1 (rango (- ?r_v (+ ?c_r2 ?c_r3))))
  (printout t "Se activa regla 26" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ ?c_r1 ?c_r2) ?c_r3))))
  (printout t "Se activa regla 27" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ ?c_r1 ?c_r2) ?c_r4))))
  (printout t "Se activa regla 28" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ ?c_r1 ?c_r4) ?c_r3))))
  (printout t "Se activa regla 29" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ ?c_r4 ?c_r2) ?c_r3))))
  (printout t "Se activa regla 30" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r4))))
  (printout t "Se activa regla 31" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r5))))
  (printout t "Se activa regla 32" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ ?c_r1 ?c_r2) ?c_r5) ?c_r4))))
  (printout t "Se activa regla 33" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ ?c_r1 ?c_r5) ?c_r3) ?c_r4))))
  (printout t "Se activa regla 34" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ ?c_r5 ?c_r2) ?c_r3) ?c_r4))))
  (printout t "Se activa regla 35" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r4) ?c_r5))))
  (printout t "Se activa regla 36" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r4) ?c_r6))))
  (printout t "Se activa regla 37" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r2) ?c_r3) ?c_r6) ?c_r5))))
  (printout t "Se activa regla 38" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r2) ?c_r6) ?c_r4) ?c_r5))))
  (printout t "Se activa regla 39" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ (+ ?c_r1 ?c_r6) ?c_r3) ?c_r4) ?c_r5))))
  (printout t "Se activa regla 40" crlf)
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
  (modify ?h1 (rango (- ?r_v (+ (+ (+ (+ ?c_r6 ?c_r2) ?c_r3) ?c_r4) ?c_r5))))
  (printout t "Se activa regla 41" crlf)
)

;;; Sumas únicas de 2 casillas

;;; Regla 42
(defrule suma-unica-2c-3
  (restriccion (valor 3) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 2))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 2))
  =>
  (modify ?h1 (rango 1 2))
  (modify ?h2 (rango 1 2))
  (printout t "Suma unica 2c 3 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Regla 43
(defrule suma-unica-2c-4
  (restriccion (valor 4) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 2))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 2))
  =>
  (modify ?h1 (rango 1 3))
  (modify ?h2 (rango 1 3))
  (printout t "Suma unica 2c 4 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Regla 44
(defrule suma-unica-2c-16
  (restriccion (valor 16) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 2))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 2))
  =>
  (modify ?h1 (rango 8 9))
  (modify ?h2 (rango 8 9))
  (printout t "Suma unica 2c 16 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Regla 45
(defrule suma-unica-2c-17
  (restriccion (valor 17) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 2))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 2))
  =>
  (modify ?h1 (rango 7 9))
  (modify ?h2 (rango 7 9))
  (printout t "Suma unica 2c 17 -> " ?r_c1 " , " ?r_c2 crlf)
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
