;;; IC: Trabajo (2017/2018)
;;; Resolución deductiva de un Kakuro
;;; Departamento de Ciencias de la Computación e Inteligencia Artificial
;;; Universidad de Sevilla
;;;============================================================================


;;;============================================================================
;;; Representación del Kakuro
;;;============================================================================

;;;   Utilizaremos la siguiente plantilla para representar las celdas del
;;; Kakuro. Cada celda tiene los siguientes campos:
;;; - id: Identificador único de la celda
;;; - fila: Número de fila en la que se encuentra la celda
;;; - columna: Número de columna en la que se encuentra la celda
;;; - rango: Rango de valores que se pueden colocar en la celda. Inicialmente
;;;   el rango son todos los valores numéricos de 1 a 9.

(deftemplate celda
  (slot id)
  (slot fila)
  (slot columna)
  (multislot rango
             (default (create$ 1 2 3 4 5 6 7 8 9))))

;;;   De esta forma, una celda tendrá un valor asignado si y solo si dicho
;;; valor es el único elemento del rango.

;;;   La siguiente variable global sirve enumerar las restricciones del puzle.

(defglobal ?*restricciones* = 0)

;;;   La siguiente función sirve para asignar de forma automática y única
;;; identificadores a las restricciones del puzle.

(deffunction idRestriccion ()
  (bind ?*restricciones* (+ ?*restricciones* 1))
  ?*restricciones*)

;;;   Utilizaremos la siguiente plantilla para almacenar las restricciones del
;;; puzle. Cada restricción tiene los siguientes campos:
;;; - id: Identificador único de la restricción
;;; - valor: Valor de la restricción
;;; - casillas: Identificadores de las casillas que se ven afectadas por la
;;;   restricción

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

(defglobal ?*AltaPrioidad* = 20)
(defglobal ?*BajaPrioidad* = -5)

(deftemplate basura
  (slot id)
  (multislot rango)
)

;*****************************************;
;* REGLAS DE PRIORIDAD ALTA (5 reglas) **;
;*****************************************;

;;; En caso de existir basura generada por las reglas de baja prioridad, la elimina
(defrule elimina-basura
  (declare (salience ?*AltaPrioidad*))
  ?h1 <- (basura (id ?b_id) (rango $?b_r))
  ?h2 <- (celda (id ?b_id) (rango $?c_ini ?c_r $?c_fin))
  (test (not (member ?c_r $?b_r)))
  =>
  (modify ?h2 (rango $?c_ini $?c_fin))
  (if (= (length $?b_r) (+ (length $?c_ini) (length $?c_fin)))
    then
    (retract ?h1)
  )
  (printout t "Elimina basura (" ?c_r ") -> " ?b_id crlf)
)

;;; Eliminar los valores de las celdas mayores a los de las restricciones
(defrule elimina-mayores-a-restricciones
  (declare (salience ?*AltaPrioidad*))
  (restriccion (id ?) (valor ?r_v) (casillas $?r_ini ?r_c $?r_fin))
  ?h <- (celda (id ?r_c) (rango $?c_ini ?c_r&:(>= ?c_r ?r_v) $?c_fin))
  =>
  (modify ?h (rango $?c_ini $?c_fin))
  (printout t "Elimina valor imposible por restriccion" crlf)
)

;;; Si es par y menor-igual que 18, no puede estar el valor/2 en ninguna casilla
(defrule elimina-mitad-si-par-menor-igual-18
  (declare (salience ?*AltaPrioidad*))
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2))
  (test (and
            (= (mod ?r_v 2) 0)
            (<= ?r_v 18)
        )
  )
  ?h1 <- (celda (id ?r_c1) (rango $?c1_r_ini ?c1_v $?c1_r_fin))
  (test (= (/ ?r_v 2) ?c1_v))
  ?h2 <- (celda (id ?r_c2) (rango $?c2_r_ini ?c2_v $?c2_r_fin))
  (test (= (/ ?r_v 2) ?c2_v))
  =>
  (modify ?h1 (rango $?c1_r_ini $?c1_r_fin))
  (modify ?h2 (rango $?c2_r_ini $?c2_r_fin))
  (printout t "Elimina mitad si es par y <= 18 (" ?r_v ") -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Eliminar los valores ya asignados en las filas
(defrule elimina-asignados-fila
  (declare (salience ?*AltaPrioidad*))
  (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  (celda (id ?r_c) (fila ?c2_f) (columna ?c2_c) (rango $?c2_r_ini ?c2_r&:(<= ?c2_r ?r_v) $?c2_r_fin))
  ?h3 <- (celda (id ?c3_id&~?r_c) (fila ?c2_f) (columna ?c3_c&~?c2_c) (rango $?c3_r_ini ?c2_r $?c3_r_fin))
  (test (and
            (= (length $?c2_r_ini) 0)
            (= (length $?c2_r_fin) 0)
        )
  )
  (test (or
           (> (length $?c3_r_ini) 0)
           (> (length $?c3_r_fin) 0)
        )
  )
  (test (or
           (member ?c3_id $?r_c_ini)
           (member ?c3_id $?r_c_fin)
        )
  )
  =>
  (modify ?h3 (rango $?c3_r_ini $?c3_r_fin))
  (printout t "Elimina valores ya asignados en fila -> "
              ?c3_id "(" ?c2_r ")" crlf)
)

;;; Eliminar los valores ya asignados en las columnas
(defrule elimina-asignados-columna
  (declare (salience ?*AltaPrioidad*))
  (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  (celda (id ?r_c)
         (fila ?c2_f)
         (columna ?c2_c)
         (rango $?c2_r_ini ?c2_r&:(<= ?c2_r ?r_v) $?c2_r_fin))
  ?h3 <- (celda (id ?c3_id&~?r_c)
                (fila ?c3_f&~?c2_f)
                (columna ?c2_c)
                (rango $?c3_r_ini ?c2_r $?c3_r_fin))
  (test (and
            (= (length $?c2_r_ini) 0)
            (= (length $?c2_r_fin) 0)
        )
  )
  (test (or
           (> (length $?c3_r_ini) 0)
           (> (length $?c3_r_fin) 0)
        )
  )
  (test (or
           (member ?c3_id $?r_c_ini)
           (member ?c3_id $?r_c_fin)
        )
  )
  =>
  (modify ?h3 (rango $?c3_r_ini $?c3_r_fin))
  (printout t "Elimina valores ya asignados en columna -> "
              ?c3_id "(" ?c2_r ")" crlf)
)

;******************************************;
;* REGLAS DE PRIORIDAD MEDIA (54 reglas) **;
;******************************************;

;;; Suma única para restricción de 2 casillas y valor 3
(defrule suma-unica-2c-3
  (restriccion (valor 3) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango  $?c_r2))
  (test (or
           (> (length $?c_r1) 2)
           (> (length $?c_r2) 2)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
  )
  (modify ?h2 (rango $?c_r))

  (printout t "Suma unica 2c 3 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Suma única para restricción de 2 casillas y valor 4
(defrule suma-unica-2c-4
  (restriccion (valor 4) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (or
           (> (length (create$ $?c_r1)) 2)
           (> (length (create$ $?c_r2)) 2)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
  )
  (modify ?h2 (rango $?c_r))

  (printout t "Suma unica 2c 4 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Suma única para restricción de 2 casillas y valor 16
(defrule suma-unica-2c-16
  (restriccion (valor 16) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (or
            (> (length (create$ $?c_r2)) 2)
            (> (length (create$ $?c_r1)) 2)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h2 (rango $?c_r))

  (printout t "Suma unica 2c 16 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Suma única para restricción de 2 casillas y valor 17
(defrule suma-unica-2c-17
  (restriccion (valor 17) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (or
           (> (length $?c_r2) 2)
           (> (length $?c_r1) 2)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h2 (rango $?c_r))
  (printout t "Suma unica 2c 17 -> " ?r_c1 " , " ?r_c2 crlf)
)

;;; Suma única para restricción de 3 casillas y valor 6
(defrule suma-unica-3c-6
  (restriccion (valor 6) (casillas ?r_c1 ?r_c2 ?r_c3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (or
           (> (length $?c_r1) 3)
           (> (length $?c_r2) 3)
           (> (length $?c_r3) 3)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
  )
  (modify ?h3 (rango $?c_r))

  (printout t "Suma unica 3c 6 -> " ?r_c1 " , " ?r_c2 " , " ?r_c3 crlf)
)

;;; Suma única para restricción de 3 casillas y valor 7
(defrule suma-unica-3c-7
  (restriccion (valor 7) (casillas ?r_c1 ?r_c2 ?r_c3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (or
           (> (length (create$ $?c_r1)) 3)
           (> (length (create$ $?c_r2)) 3)
           (> (length (create$ $?c_r3)) 3)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
  )
  (modify ?h3 (rango $?c_r))

  (printout t "Suma unica 3c 7 -> " ?r_c1 " , " ?r_c2 " , " ?r_c3 crlf)
)

;;; Suma única para restricción de 3 casillas y valor 23
(defrule suma-unica-3c-23
  (restriccion (valor 23) (casillas ?r_c1 ?r_c2 ?r_c3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (or
           (> (length (create$ $?c_r1)) 3)
           (> (length (create$ $?c_r2)) 3)
           (> (length (create$ $?c_r3)) 3)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h3 (rango $?c_r))

  (printout t "Suma unica 3c 23 -> " ?r_c1 " , " ?r_c2 " , " ?r_c3 crlf)
)

;;; Suma única para restricción de 3 casillas y valor 24
(defrule suma-unica-3c-24
  (restriccion (valor 24) (casillas ?r_c1 ?r_c2 ?r_c3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (or
           (> (length $?c_r1) 3)
           (> (length $?c_r2) 3)
           (> (length $?c_r3) 3)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h3 (rango $?c_r))

  (printout t "Suma unica 3c 24 -> " ?r_c1 " , " ?r_c2 " , " ?r_c3 crlf)
)

;;; Suma única para restricción de 4 casillas y valor 10
(defrule suma-unica-4c-10
  (restriccion (valor 10) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (or
           (> (length $?c_r1) 4)
           (> (length $?c_r2) 4)
           (> (length $?c_r3) 4)
           (> (length $?c_r4) 4)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
  )
  (modify ?h3 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r4)) do
    (bind ?a (nth$ ?i $?c_r4))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
  )
  (modify ?h4 (rango $?c_r))

  (printout t "Suma unica 4c 10 -> " ?r_c1 " , "
                                     ?r_c2 " , "
                                     ?r_c3 " , "
                                     ?r_c4 crlf)
)

;;; Suma única para restricción de 4 casillas y valor 11
(defrule suma-unica-4c-11
  (restriccion (valor 11) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (or
           (> (length $?c_r1) 4)
           (> (length $?c_r2) 4)
           (> (length $?c_r3) 4)
           (> (length $?c_r4) 4)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
  )
  (modify ?h3 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r4)) do
    (bind ?a (nth$ ?i $?c_r4))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
  )
  (modify ?h4 (rango $?c_r))

  (printout t "Suma unica 4c 11 -> " ?r_c1 " , "
                                     ?r_c2 " , "
                                     ?r_c3 " , "
                                     ?r_c4 crlf)
)

;;; Suma única para restricción de 4 casillas y valor 29
(defrule suma-unica-4c-29
  (restriccion (valor 29) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (or
           (> (length $?c_r1) 4)
           (> (length $?c_r2) 4)
           (> (length $?c_r3) 4)
           (> (length $?c_r4) 4)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h3 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r4)) do
    (bind ?a (nth$ ?i $?c_r4))
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h4 (rango $?c_r))

  (printout t "Suma unica 4c 29 -> " ?r_c1 " , "
                                     ?r_c2 " , "
                                     ?r_c3 " , "
                                     ?r_c4 crlf)
)

;;; Suma única para restricción de 4 casillas y valor 30
(defrule suma-unica-4c-30
  (restriccion (valor 30) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (or
           (> (length $?c_r1) 4)
           (> (length $?c_r2) 4)
           (> (length $?c_r3) 4)
           (> (length $?c_r4) 4)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h3 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r4)) do
    (bind ?a (nth$ ?i $?c_r4))
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h4 (rango $?c_r))

  (printout t "Suma unica 4c 30 -> " ?r_c1 " , "
                                     ?r_c2 " , "
                                     ?r_c3 " , "
                                     ?r_c4 crlf)
)

;;; Suma única para restricción de 5 casillas y valor 15
(defrule suma-unica-5c-15
  (restriccion (valor 15) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  ?h5 <- (celda (id ?r_c5) (rango $?c_r5))
  (test (or
           (> (length $?c_r1) 5)
           (> (length $?c_r2) 5)
           (> (length $?c_r3) 5)
           (> (length $?c_r4) 5)
           (> (length $?c_r5) 5)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
  )
  (modify ?h3 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r4)) do
    (bind ?a (nth$ ?i $?c_r4))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
  )
  (modify ?h4 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r5)) do
    (bind ?a (nth$ ?i $?c_r5))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
  )
  (modify ?h5 (rango $?c_r))

  (printout t "Suma unica 5c 15 -> " ?r_c1 " , "
                                     ?r_c2 " , "
                                     ?r_c3 " , "
                                     ?r_c4 " , "
                                     ?r_c5 crlf)
)

;;; Suma única para restricción de 5 casillas y valor 16
(defrule suma-unica-5c-16
  (restriccion (valor 16) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  ?h5 <- (celda (id ?r_c5) (rango $?c_r5))
  (test (or
           (> (length $?c_r1) 5)
           (> (length $?c_r2) 5)
           (> (length $?c_r3) 5)
           (> (length $?c_r4) 5)
           (> (length $?c_r5) 5)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
  )
  (modify ?h3 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r4)) do
    (bind ?a (nth$ ?i $?c_r4))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
  )
  (modify ?h4 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r5)) do
    (bind ?a (nth$ ?i $?c_r5))
    (if (= ?a 1)
      then
      (bind $?c_r  (create$ $?c_r 1))
    )
    (if (= ?a 2)
      then
      (bind $?c_r  (create$ $?c_r 2))
    )
    (if (= ?a 3)
      then
      (bind $?c_r  (create$ $?c_r 3))
    )
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
  )
  (modify ?h5 (rango $?c_r))

  (printout t "Suma unica 5c 16 -> " ?r_c1 " , "
                                     ?r_c2 " , "
                                     ?r_c3 " , "
                                     ?r_c4 " , "
                                     ?r_c5 crlf)
)

;;; Suma única para restricción de 5 casillas y valor 34
(defrule suma-unica-5c-34
  (restriccion (valor 34) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  ?h5 <- (celda (id ?r_c5) (rango $?c_r5))
  (test (or
           (> (length $?c_r1) 5)
           (> (length $?c_r2) 5)
           (> (length $?c_r3) 5)
           (> (length $?c_r4) 5)
           (> (length $?c_r5) 5)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h3 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r4)) do
    (bind ?a (nth$ ?i $?c_r4))
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h4 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r5)) do
    (bind ?a (nth$ ?i $?c_r5))
    (if (= ?a 4)
      then
      (bind $?c_r  (create$ $?c_r 4))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h5 (rango $?c_r))

  (printout t "Suma unica 5c 34 -> " ?r_c1 " , "
                                     ?r_c2 " , "
                                     ?r_c3 " , "
                                     ?r_c4 " , "
                                     ?r_c5 crlf)
)

;;; Suma única para restricción de 5 casillas y valor 35
(defrule suma-unica-5c-35
  (restriccion (valor 35) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  ?h5 <- (celda (id ?r_c5) (rango $?c_r5))
  (test (or
           (> (length $?c_r1) 5)
           (> (length $?c_r2) 5)
           (> (length $?c_r3) 5)
           (> (length $?c_r4) 5)
           (> (length $?c_r5) 5)
        )
  )
  =>
  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h1 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r2)) do
    (bind ?a (nth$ ?i $?c_r2))
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h2 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r3)) do
    (bind ?a (nth$ ?i $?c_r3))
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h3 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r4)) do
    (bind ?a (nth$ ?i $?c_r4))
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h4 (rango $?c_r))

  (bind $?c_r (create$))
  (loop-for-count (?i 1 (length $?c_r5)) do
    (bind ?a (nth$ ?i $?c_r5))
    (if (= ?a 5)
      then
      (bind $?c_r  (create$ $?c_r 5))
    )
    (if (= ?a 6)
      then
      (bind $?c_r  (create$ $?c_r 6))
    )
    (if (= ?a 7)
      then
      (bind $?c_r  (create$ $?c_r 7))
    )
    (if (= ?a 8)
      then
      (bind $?c_r  (create$ $?c_r 8))
    )
    (if (= ?a 9)
      then
      (bind $?c_r  (create$ $?c_r 9))
    )
  )
  (modify ?h5 (rango $?c_r))

  (printout t "Suma unica 5c 35 -> " ?r_c1 " , "
                                     ?r_c2 " , "
                                     ?r_c3 " , "
                                     ?r_c4 " , "
                                     ?r_c5 crlf)
)

;;; Números comunes (restricción 2 a 2 de 17 y 16)
(defrule restriccion-2-a-2-de-17-16
  (restriccion (valor ?r1_v&:(= ?r1_v 17))
               (casillas $?r1_c_ini ?r1_c $?r1_c_fin))
  (restriccion (valor ?r2_v&:(= ?r2_v 16))
               (casillas $?r2_c_ini ?r2_c $?r2_c_fin))
  (test (= (+ (length $?r1_c_ini) (length $?r1_c_fin) 1) 2))
  (test (= (+ (length $?r2_c_ini) (length $?r2_c_fin) 1) 2))
  (test (= ?r1_c ?r2_c))
  ?h1 <- (celda (id ?r1_c) (rango $?h1_ini ?r_c_v&:(= ?r_c_v 9) $?h1_fin))
  (test (> (+ (length $?h1_ini) (length $?h1_fin) 1) 1))
  =>
  (modify ?h1 (rango 9))
  (printout t "Restriccion 2 a 2 de valor 17 y 16 -> " ?r1_c "(9)" crlf)
)

;;; Par oculto fila
(defrule par-asignado-fila
  ?h1 <- (celda (id ?c1_id) (fila ?c_f) (rango ?v1 ?v2))
  ?h2 <- (celda (id ?c2_id) (fila ?c_f) (rango ?v1 ?v2))
  (test (neq ?h1 ?h2))
  (restriccion (casillas $?r_c))
  (test (and
            (member ?c1_id $?r_c)
            (member ?c2_id $?r_c)
        )
  )
  ?h3 <- (celda (id ?c3_id) (fila ?c_f) (rango $?ini ?v&?v1|?v2 $?fin))
  (test (member ?c3_id $?r_c))
  (test (and
            (neq ?h1 ?h3)
            (neq ?h2 ?h3)
        )
  )
  =>
  (modify ?h3 (rango $?ini $?fin))
  (printout t "Par oculto fila para valores (" ?v1 " " ?v2
              ") en celda " ?c3_id " (quita " ?v ")" crlf)
)

;;; Par oculto columna
(defrule par-asignado-columna
  ?h1 <- (celda (id ?c1_id) (columna ?c_c) (rango ?v1 ?v2))
  ?h2 <- (celda (id ?c2_id) (columna ?c_c) (rango ?v1 ?v2))
  (test (neq ?h1 ?h2))
  (restriccion (casillas $?r_c))
  (test (and
            (member ?c1_id $?r_c)
            (member ?c2_id $?r_c)
        )
  )
  ?h3 <- (celda (id ?c3_id) (columna ?c_c) (rango $?ini ?v&?v1|?v2 $?fin))
  (test (member ?c3_id $?r_c))
  (test (and
            (neq ?h1 ?h3)
            (neq ?h2 ?h3)
        )
  )
  =>
  (modify ?h3 (rango $?ini $?fin))
  (printout t "Par oculto columna para valores (" ?v1 " " ?v2
              ") en celda " ?c3_id " (quita " ?v ")" crlf)
)

;;; Trío oculto fila
(defrule trio-asignado-fila
  ?h1 <- (celda (id ?c1_id) (fila ?c_f) (rango ?v1 ?v2 ?v3))
  ?h2 <- (celda (id ?c2_id) (fila ?c_f) (rango ?v1 ?v2 ?v3))
  ?h3 <- (celda (id ?c3_id) (fila ?c_f) (rango ?v1 ?v2 ?v3))
  (test (and (and (neq ?h1 ?h2) (neq ?h1 ?h3)) (neq ?h2 ?h3)))
  (restriccion (casillas $?r_c))
  (test (and
            (member ?c1_id $?r_c)
            (member ?c2_id $?r_c)
            (member ?c3_id $?r_c)
        )
  )
  ?h4 <- (celda (id ?c4_id) (fila ?c_f) (rango $?ini ?v&?v1|?v2|?v3 $?fin))
  (test (member ?c4_id $?r_c))
  (test (and
            (neq ?h1 ?h4)
            (neq ?h2 ?h4)
            (neq ?h3 ?h4)
        )
  )
  =>
  (modify ?h4 (rango $?ini $?fin))
  (printout t "Trio oculto fila para valores (" ?v1 " " ?v2 " " ?v3
              ") en celda " ?c4_id " (quita " ?v ")" crlf)
)

;;; Trío oculto columna
(defrule trio-asignado-columna
  ?h1 <- (celda (id ?c1_id) (columna ?c_c) (rango ?v1 ?v2 ?v3))
  ?h2 <- (celda (id ?c2_id) (columna ?c_c) (rango ?v1 ?v2 ?v3))
  ?h3 <- (celda (id ?c3_id) (columna ?c_c) (rango ?v1 ?v2 ?v3))
  (test (and
            (neq ?h1 ?h2)
            (neq ?h1 ?h3)
            (neq ?h2 ?h3)
        )
  )
  (restriccion (casillas $?r_c))
  (test (and
            (member ?c1_id $?r_c)
            (member ?c2_id $?r_c)
            (member ?c3_id $?r_c)
        )
  )
  ?h4 <- (celda (id ?c4_id) (columna ?c_c) (rango $?ini ?v&?v1|?v2|?v3 $?fin))
  (test (member ?c4_id $?r_c))
  (test (and
            (neq ?h1 ?h4)
            (neq ?h2 ?h4)
            (neq ?h3 ?h4)
        )
  )
  =>
  (modify ?h4 (rango $?ini $?fin))
  (printout t "Trio oculto columna para valores (" ?v1 " " ?v2 " " ?v3
              ") en celda " ?c4_id " (quita " ?v ")" crlf)
)

;;; Valores máximos (2 casillas)
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
  (printout t "Valores maximos 2c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v ")" crlf)
)

;;; Valores máximos (3 casillas)
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
  (printout t "Valores maximos 3c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v "), "
                                       ?v3 "(" ?c3_v ")" crlf)
)

;;; Valores máximos (4 casillas)
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
  (test (= (+ ?c1_v ?c2_v ?c3_v ?c4_v) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (modify ?h4 (rango ?c4_v))
  (printout t "Valores maximos 4c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v "), "
                                       ?v3 "(" ?c3_v "), "
                                       ?v4 "(" ?c4_v ")" crlf)
)

;;; Valores máximos (5 casillas)
(defrule max-valores-5
  (restriccion (valor ?r_v) (casillas ?v1 ?v2 ?v3 ?v4 ?v5))
  ?h1 <- (celda (id ?v1) (rango $?c1_ini ?c1_v))
  (test (> (+ (length $?c1_ini) 1) 1))
  ?h2 <- (celda (id ?v2) (rango $?c2_ini ?c2_v))
  (test (> (+ (length $?c2_ini) 1) 1))
  ?h3 <- (celda (id ?v3) (rango $?c3_ini ?c3_v))
  (test (> (+ (length $?c3_ini) 1) 1))
  ?h4 <- (celda (id ?v4) (rango $?c4_ini ?c4_v))
  (test (> (+ (length $?c4_ini) 1) 1))
  ?h5 <- (celda (id ?v5) (rango $?c5_ini ?c5_v))
  (test (> (+ (length $?c5_ini) 1) 1))
  (test (= (+ ?c1_v ?c2_v ?c3_v ?c4_v ?c5_v) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (modify ?h4 (rango ?c4_v))
  (modify ?h5 (rango ?c5_v))
  (printout t "Valores maximos 5c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v "), "
                                       ?v3 "(" ?c3_v "), "
                                       ?v4 "(" ?c4_v "), "
                                       ?v5 "(" ?c5_v ")" crlf)
)

;;; Valores máximos (6 casillas)
(defrule max-valores-6
  (restriccion (valor ?r_v) (casillas ?v1 ?v2 ?v3 ?v4 ?v5 ?v6))
  ?h1 <- (celda (id ?v1) (rango $?c1_ini ?c1_v))
  (test (> (+ (length $?c1_ini) 1) 1))
  ?h2 <- (celda (id ?v2) (rango $?c2_ini ?c2_v))
  (test (> (+ (length $?c2_ini) 1) 1))
  ?h3 <- (celda (id ?v3) (rango $?c3_ini ?c3_v))
  (test (> (+ (length $?c3_ini) 1) 1))
  ?h4 <- (celda (id ?v4) (rango $?c4_ini ?c4_v))
  (test (> (+ (length $?c4_ini) 1) 1))
  ?h5 <- (celda (id ?v5) (rango $?c5_ini ?c5_v))
  (test (> (+ (length $?c5_ini) 1) 1))
  ?h6 <- (celda (id ?v6) (rango $?c6_ini ?c6_v))
  (test (> (+ (length $?c6_ini) 1) 1))
  (test (= (+ ?c1_v ?c2_v ?c3_v ?c4_v ?c5_v ?c6_v) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (modify ?h4 (rango ?c4_v))
  (modify ?h5 (rango ?c5_v))
  (modify ?h6 (rango ?c6_v))
  (printout t "Valores maximos 6c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v "), "
                                       ?v3 "(" ?c3_v "), "
                                       ?v4 "(" ?c4_v "), "
                                       ?v5 "(" ?c5_v ")" crlf)
)

;;; Valores mínimos (2 casillas)
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
  (printout t "Valores minimos 2c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v ")" crlf)
)

;;; Valores mínimos (3 casillas)
(defrule min-valores-3
  (restriccion (valor ?r_v) (casillas ?v1 ?v2 ?v3))
  ?h1 <- (celda (id ?v1) (rango ?c1_v $?c1_fin))
  (test (> (+ (length $?c1_fin) 1) 1))
  ?h2 <- (celda (id ?v2) (rango ?c2_v&~?c1_v $?c2_fin))
  (test (> (+ (length $?c2_fin) 1) 1))
  ?h3 <- (celda (id ?v3) (rango ?c3_v&~?c1_v&~?c2_v $?c3_fin))
  (test (> (+ (length $?c3_fin) 1) 1))
  (test (= (+ ?c1_v ?c2_v ?c3_v) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (printout t "Valores minimos 3c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v "), "
                                       ?v3 "(" ?c3_v ")" crlf)
)

;;; Valores mínimos (4 casillas)
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
  (test (= (+ ?c1_v ?c2_v ?c3_v ?c4_v) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (modify ?h4 (rango ?c4_v))
  (printout t "Valores minimos 4c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v "), "
                                       ?v3 "(" ?c3_v "), "
                                       ?v4 "(" ?c4_v ")" crlf)
)

;;; Valores mínimos (5 casillas)
(defrule min-valores-5
  (restriccion (valor ?r_v) (casillas ?v1 ?v2 ?v3 ?v4 ?v5))
  ?h1 <- (celda (id ?v1) (rango ?c1_v $?c1_fin))
  (test (> (+ (length $?c1_fin) 1) 1))
  ?h2 <- (celda (id ?v2) (rango ?c2_v $?c2_fin))
  (test (> (+ (length $?c2_fin) 1) 1))
  ?h3 <- (celda (id ?v3) (rango ?c3_v $?c3_fin))
  (test (> (+ (length $?c3_fin) 1) 1))
  ?h4 <- (celda (id ?v4) (rango ?c4_v $?c4_fin))
  (test (> (+ (length $?c4_fin) 1) 1))
  ?h5 <- (celda (id ?v5) (rango ?c5_v $?c5_fin))
  (test (> (+ (length $?c5_fin) 1) 1))
  (test (= (+ ?c1_v ?c2_v ?c3_v ?c4_v ?c5_v) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (modify ?h4 (rango ?c4_v))
  (modify ?h5 (rango ?c5_v))
  (printout t "Valores minimos 5c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v "), "
                                       ?v3 "(" ?c3_v "), "
                                       ?v4 "(" ?c4_v "), "
                                       ?v5 "(" ?c5_v ")" crlf)
)

;;; Valores mínimos (6 casillas)
(defrule min-valores-6
  (restriccion (valor ?r_v) (casillas ?v1 ?v2 ?v3 ?v4 ?v5 ?v6))
  ?h1 <- (celda (id ?v1) (rango ?c1_v $?c1_fin))
  (test (> (+ (length $?c1_fin) 1) 1))
  ?h2 <- (celda (id ?v2) (rango ?c2_v $?c2_fin))
  (test (> (+ (length $?c2_fin) 1) 1))
  ?h3 <- (celda (id ?v3) (rango ?c3_v $?c3_fin))
  (test (> (+ (length $?c3_fin) 1) 1))
  ?h4 <- (celda (id ?v4) (rango ?c4_v $?c4_fin))
  (test (> (+ (length $?c4_fin) 1) 1))
  ?h5 <- (celda (id ?v5) (rango ?c5_v $?c5_fin))
  (test (> (+ (length $?c5_fin) 1) 1))
  ?h6 <- (celda (id ?v6) (rango ?c6_v $?c6_fin))
  (test (> (+ (length $?c6_fin) 1) 1))
  (test (= (+ ?c1_v ?c2_v ?c3_v ?c4_v ?c5_v ?c6_v) ?r_v))
  =>
  (modify ?h1 (rango ?c1_v))
  (modify ?h2 (rango ?c2_v))
  (modify ?h3 (rango ?c3_v))
  (modify ?h4 (rango ?c4_v))
  (modify ?h5 (rango ?c5_v))
  (modify ?h6 (rango ?c6_v))
  (printout t "Valores minimos 6c -> " ?v1 "(" ?c1_v "), "
                                       ?v2 "(" ?c2_v "), "
                                       ?v3 "(" ?c3_v "), "
                                       ?v4 "(" ?c4_v "), "
                                       ?v5 "(" ?c5_v "), "
                                       ?v6 "(" ?c6_v ")" crlf)
)

;;; Detecta cuadrado (2x2) con una restricción de 3 casillas
(defrule detecta-cuadro-con-1-extra
  (restriccion (valor ?r1_v) (casillas ?r1_c1 ?r1_c2))
  (restriccion (valor ?r2_v) (casillas ?r2_c1 ?r2_c2))
  (restriccion (valor ?r3_v) (casillas ?r1_c1 ?r2_c1))
  (restriccion (valor ?r4_v) (casillas ?r1_c2 ?r2_c2 ?r4_c3))
  ?h1 <- (celda (id ?r4_c3) (rango $?c_r))
  (test (> (length $?c_r) 1))
  =>
  (bind ?result (abs (- (+ ?r1_v ?r2_v) ?r3_v ?r4_v)))
  (modify ?h1 (rango ?result))
  (printout t "Detecta 2x2 con 1 extra -> " ?r4_c3 "(" ?result ")"  crlf)
)

;;; Detecta cuadrado (2x2) con una restricción de 3 casillas
(defrule detecta-cuadro-con-1-extra-2
  (restriccion (valor ?r1_v) (casillas ?r1_c1 ?r1_c2))
  (restriccion (valor ?r2_v) (casillas ?r2_c1 ?r2_c2))
  (restriccion (valor ?r3_v) (casillas ?r1_c2 ?r2_c2))
  (restriccion (valor ?r4_v) (casillas ?r1_c1 ?r2_c1 ?r4_c3))
  ?h1 <- (celda (id ?r4_c3) (rango $?c_r))
  (test (> (length $?c_r) 1))
  =>
  (bind ?result (abs (- (+ ?r1_v ?r2_v) ?r3_v ?r4_v)))
  (modify ?h1 (rango ?result))
  (printout t "Detecta 2x2 con 1 extra -> " ?r4_c3 "(" ?result ")"  crlf)
)

;;; Detecta cuadrado (2x2) con una restricción de 3 casillas
(defrule detecta-cuadro-con-1-extra-3
  (restriccion (valor ?r1_v) (casillas ?r1_c1 ?r1_c2))
  (restriccion (valor ?r2_v) (casillas ?r2_c1 ?r2_c2))
  (restriccion (valor ?r3_v) (casillas ?r1_c1 ?r2_c1))
  (restriccion (valor ?r4_v) (casillas ?r4_c3 ?r1_c2 ?r2_c2))
  ?h1 <- (celda (id ?r4_c3) (rango $?c_r))
  (test (> (length $?c_r) 1))
  =>
  (bind ?result (abs (- (+ ?r1_v ?r2_v) ?r3_v ?r4_v)))
  (modify ?h1 (rango ?result))
  (printout t "Detecta 2x2 con 1 extra -> " ?r4_c3 "(" ?result ")"  crlf)
)

;;; Detecta cuadrado (2x2) con una restricción de 3 casillas
(defrule detecta-cuadro-con-1-extra-4
  (restriccion (valor ?r1_v) (casillas ?r1_c1 ?r1_c2))
  (restriccion (valor ?r2_v) (casillas ?r2_c1 ?r2_c2))
  (restriccion (valor ?r3_v) (casillas ?r1_c2 ?r2_c2))
  (restriccion (valor ?r4_v) (casillas ?r4_c3 ?r1_c1 ?r2_c1))
  ?h1 <- (celda (id ?r4_c3) (rango $?c_r))
  (test (> (length $?c_r) 1))
  =>
  (bind ?result (abs (- (+ ?r1_v ?r2_v) ?r3_v ?r4_v)))
  (modify ?h1 (rango ?result))
  (printout t "Detecta 2x2 con 1 extra -> " ?r4_c3 "(" ?result ")"  crlf)
)

;;; Completa una restriccion de 2 casillas en el que 1 esté resuelta
(defrule completa-2
  (celda (id ?c_c) (rango ?c_v))
  (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  (test (= (+ (length $?r_c_ini) (length $?r_c_fin) 1) 2))
  (test (member ?c_c (create$ $?r_c_ini ?r_c $?r_c_fin)))
  ?h1 <- (celda (id ?r_c&~?c_c) (rango $?h1_r))
  (test (> (length $?h1_r) 1))
  =>
  (bind ?result (- ?r_v ?c_v))
  (modify ?h1 (rango ?result))
  (printout t "Completa 2c -> " ?r_c " con valor " ?result crlf)
)

;;; Completa una restricción de 3 con 2 casillas resueltas
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

;;; Completa una restricción de 3 con 2 casillas resueltas
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

;;; Completa una restricción de 3 con 2 casillas resueltas
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

;;; Completa una restricción de 4 con 3 casillas resueltas
(defrule completa-4-1
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (> (length $?c_r4) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2 ?c_r3)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 4c -> " ?r_c4 " con valor " ?result crlf)
)

;;; Completa una restricción de 4 con 3 casillas resueltas
(defrule completa-4-2
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (> (length $?c_r3) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2 ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 4c -> " ?r_c3 " con valor " ?result crlf)
)

;;; Completa una restricción de 4 con 3 casillas resueltas
(defrule completa-4-3
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c4) (rango ?c_r4))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r4 ?c_r3)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 4c -> " ?r_c2 " con valor " ?result crlf)
)

;;; Completa una restricción de 4 con 3 casillas resueltas
(defrule completa-4-4
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  (celda (id ?r_c4) (rango ?c_r4))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r4 ?c_r2 ?c_r3)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 4c -> " ?r_c1 " con valor " ?result crlf)
)

;;; Completa una restricción de 5 con 4 casillas resueltas
(defrule completa-5-1
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c5) (rango $?c_r5))
  (test (> (length $?c_r5) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2 ?c_r3 ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c5 " con valor " ?result crlf)
)

;;; Completa una restricción de 5 con 4 casillas resueltas
(defrule completa-5-2
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c5) (rango ?c_r5))
  ?h1 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (> (length $?c_r4) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2 ?c_r3 ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c4 " con valor " ?result crlf)
)

;;; Completa una restricción de 5 con 4 casillas resueltas
(defrule completa-5-3
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c5) (rango ?c_r5))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (> (length $?c_r3) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2 ?c_r5 ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c3 " con valor " ?result crlf)
)

;;; Completa una restricción de 5 con 4 casillas resueltas
(defrule completa-5-4
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c1) (rango ?c_r1))
  (celda (id ?r_c5) (rango ?c_r5))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (> (length $?c_r2) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r5 ?c_r3 ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c2 " con valor " ?result crlf)
)

;;; Completa una restricción de 5 con 4 casillas resueltas
(defrule completa-5-5
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  (celda (id ?r_c5) (rango ?c_r5))
  (celda (id ?r_c2) (rango ?c_r2))
  (celda (id ?r_c3) (rango ?c_r3))
  (celda (id ?r_c4) (rango ?c_r4))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  (test (> (length $?c_r1) 1))
  =>
  (bind ?result (- ?r_v (+ ?c_r5 ?c_r2 ?c_r3 ?c_r4)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 5c -> " ?r_c1 " con valor " ?result crlf)
)

;;; Completa una restricción de 6 con 5 casillas resueltas
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
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2 ?c_r3 ?c_r4 ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c6 " con valor " ?result crlf)
)

;;; Completa una restricción de 6 con 5 casillas resueltas
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
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2 ?c_r3 ?c_r4 ?c_r6)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c5 " con valor " ?result crlf)
)

;;; Completa una restricción de 6 con 5 casillas resueltas
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
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2 ?c_r3 ?c_r6 ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c4 " con valor " ?result crlf)
)

;;; Completa una restricción de 6 con 5 casillas resueltas
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
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r2 ?c_r6 ?c_r4 ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c3 " con valor " ?result crlf)
)

;;; Completa una restricción de 6 con 5 casillas resueltas
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
  (bind ?result (- ?r_v (+ ?c_r1 ?c_r6 ?c_r3 ?c_r4 ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c2 " con valor " ?result crlf)
)

;;; Completa una restricción de 6 con 5 casillas resueltas
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
  (bind ?result (- ?r_v (+ ?c_r6 ?c_r2 ?c_r3 ?c_r4 ?c_r5)))
  (modify ?h1 (rango ?result))
  (printout t "Completa 6c -> " ?r_c1 " con valor " ?result crlf)
)

;******************************************;
;* REGLAS DE PRIORIDAD BAJA (5 reglas) **;
;******************************************;

;;; Búsqueda de candidatos únicos con 2c. Genera basura en caso de existir.
(defrule busca-candidato-unico-2c
  (declare (salience ?*BajaPrioidad*))
  (restriccion (valor ?r_v&:(<= ?r_v 18)) (casillas ?r_c1 ?r_c2))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  (test (and
            (> (length $?c_r1) 1)
            (> (length $?c_r2) 1)
        )
  )
  =>
  (bind $?basura1 (create$))
  (bind $?basura2 (create$))
  (bind ?results 0)
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (loop-for-count (?j 1 (length $?c_r2)) do
      (bind ?b (nth$ ?j $?c_r2))
      (if (and
              (= ?r_v (+ ?a ?b))
              (neq ?a ?b)
          )
        then (bind ?results (+ ?results +1))
             (bind ?c_candidate1 ?a)
             (if (not (member ?a $?basura1))
                then (bind $?basura1 (create$ $?basura1 ?a))
             )
             (bind ?c_candidate2 ?b)
             (if (not (member ?b $?basura2))
                then (bind $?basura2 (create$ ?b $?basura2))
             )
      )
    )
  )
  (if (= ?results 1)
    then (modify ?h1 (rango ?c_candidate1))
         (modify ?h2 (rango ?c_candidate2))
         (printout t crlf "** Encuentra candidado unico 2c -> " ?r_c1 "(" ?c_candidate1 "), " ?r_c2 "(" ?c_candidate2 ")" crlf)
  )
  (if (> ?results 1)
    then (if (< (length $?basura1) (length $?c_r1))
            then
            (assert (basura (id ?r_c1) (rango $?basura1)))
            (printout t "Recolecta basura (2c) " ?r_c1 " - " $?basura1 crlf)
         )
         (if (< (length $?basura2) (length $?c_r2))
                 then
            (assert (basura (id ?r_c2) (rango $?basura2)))
            (printout t "Recolecta basura (2c) " ?r_c2 " - " $?basura1 crlf)
         )
  )
)

;;; Búsqueda de candidatos únicos con 3c. Genera basura en caso de existir.
(defrule busca-candidato-unico-3c ;(0 resueltas - 3 no) or (1 resuelta - 2 no)
  (declare (salience ?*BajaPrioidad*))
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  (test (or
           (and (> (length $?c_r1) 1) (> (length $?c_r2) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r3) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r3) 1))
        )
  )
  =>
  (bind $?basura1 (create$))
  (bind $?basura2 (create$))
  (bind $?basura3 (create$))
  (bind ?results 0)
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (loop-for-count (?j 1 (length $?c_r2)) do
      (bind ?b (nth$ ?j $?c_r2))
      	(loop-for-count (?k 1 (length $?c_r3)) do
      		(bind ?c (nth$ ?k $?c_r3))
      		(if (and
                  (= ?r_v (+ ?a (+ ?b ?c)))
                  (neq ?a ?b)
                  (neq ?a ?c)
                  (neq ?b ?c)
              )
        		then
           		(bind ?results (+ ?results +1))
           		(bind ?c_candidate1 ?a)
              (if (not (member ?a $?basura1))
                 then (bind $?basura1 (create$ ?a $?basura1))
              )
              (bind ?c_candidate2 ?b)
              (if (not (member ?b $?basura2))
                 then (bind $?basura2 (create$ ?b $?basura2))
              )
              (bind ?c_candidate3 ?c)
              (if (not (member ?c $?basura3))
                 then (bind $?basura3 (create$ ?c $?basura3))
              )
      		)
      	)
    )
  )
  (if (= ?results 1)
    then (modify ?h1 (rango ?c_candidate1))
         (modify ?h2 (rango ?c_candidate2))
         (modify ?h3 (rango ?c_candidate3))
         (printout t crlf "*** Encuentra candidado unico 3c -> " ?r_c1 "(" ?c_candidate1 "), " ?r_c2 "(" ?c_candidate2 "), " ?r_c3 "(" ?c_candidate3 ")" crlf)
  )
  (if (> ?results 1)
    then (if (< (length $?basura1) (length $?c_r1))
            then
            (assert (basura (id ?r_c1) (rango $?basura1)))
            (printout t "Recolecta basura (3c) " ?r_c1 " - " $?basura1 crlf)
         )
         (if (< (length $?basura2) (length $?c_r2))
                 then
            (assert (basura (id ?r_c2) (rango $?basura2)))
            (printout t "Recolecta basura (3c) " ?r_c2 " - " $?basura2 crlf)
         )
         (if (< (length $?basura3) (length $?c_r3))
                 then
            (assert (basura (id ?r_c3) (rango $?basura3)))
            (printout t "Recolecta basura (3c) " ?r_c3 " - " $?basura3 crlf)
         )
  )
)

;;; Búsqueda de candidatos únicos con 4c. Genera basura en caso de existir.
(defrule busca-candidato-unico-4c
  (declare (salience ?*BajaPrioidad*))
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  (test (or
           (and (> (length $?c_r1) 1) (> (length $?c_r2) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r3) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r4) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r3) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r4) 1))
           (and (> (length $?c_r3) 1) (> (length $?c_r4) 1))
        )
  )
  =>
  (bind $?basura1 (create$))
  (bind $?basura2 (create$))
  (bind $?basura3 (create$))
  (bind $?basura4 (create$))
  (bind ?results 0)
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (loop-for-count (?j 1 (length $?c_r2)) do
      (bind ?b (nth$ ?j $?c_r2))
      (loop-for-count (?k 1 (length $?c_r3)) do
      	(bind ?c (nth$ ?k $?c_r3))
        (loop-for-count (?w 1 (length $?c_r4)) do
          (bind ?d (nth$ ?w $?c_r4))
      		(if (and
                  (= ?r_v (+ ?a ?b ?c ?d))
                  (neq ?a ?b)
                  (neq ?a ?c)
                  (neq ?a ?d)
                  (neq ?b ?c)
                  (neq ?b ?d)
                  (neq ?c ?d)
              )
        		then
           		(bind ?results (+ ?results +1))
              (bind ?c_candidate1 ?a)
              (if (not (member ?a $?basura1))
                 then (bind $?basura1 (create$ ?a $?basura1))
              )
              (bind ?c_candidate2 ?b)
              (if (not (member ?b $?basura2))
                 then (bind $?basura2 (create$ ?b $?basura2))
              )
              (bind ?c_candidate3 ?c)
              (if (not (member ?c $?basura3))
                 then (bind $?basura3 (create$ ?c $?basura3))
              )
              (bind ?c_candidate4 ?d)
              (if (not (member ?d $?basura4))
                 then (bind $?basura4 (create$ ?d $?basura4))
              )
          )
      	)
      )
    )
  )
  (if (= ?results 1)
    then (modify ?h1 (rango ?c_candidate1))
         (modify ?h2 (rango ?c_candidate2))
         (modify ?h3 (rango ?c_candidate3))
         (modify ?h4 (rango ?c_candidate4))
         (printout t crlf "**** Encuentra candidado unico 4c -> " ?r_c1 "(" ?c_candidate1 "), " ?r_c2 "(" ?c_candidate2 "), " ?r_c3 "(" ?c_candidate3 "), " ?r_c4 "(" ?c_candidate4 ")" crlf)
  )
  (if (> ?results 1)
    then (if (< (length $?basura1) (length $?c_r1))
            then
            (assert (basura (id ?r_c1) (rango $?basura1)))
            (printout t "Recolecta basura (4c) " ?r_c1 " - " $?basura1 crlf)
         )
         (if (< (length $?basura2) (length $?c_r2))
                 then
            (assert (basura (id ?r_c2) (rango $?basura2)))
            (printout t "Recolecta basura (4c) " ?r_c2 " - " $?basura2 crlf)
         )
         (if (< (length $?basura3) (length $?c_r3))
                 then
            (assert (basura (id ?r_c3) (rango $?basura3)))
            (printout t "Recolecta basura (4c) " ?r_c3 " - " $?basura3 crlf)
         )
         (if (< (length $?basura4) (length $?c_r4))
                 then
            (assert (basura (id ?r_c4) (rango $?basura4)))
            (printout t "Recolecta basura (4c) " ?r_c4 " - " $?basura4 crlf)
         )
  )
)

;;; Búsqueda de candidatos únicos con 5c. Genera basura en caso de existir.
(defrule busca-candidato-unico-5c
  (declare (salience ?*BajaPrioidad*))
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  ?h5 <- (celda (id ?r_c5) (rango $?c_r5))
  (test (or
           (and (> (length $?c_r4) 1) (> (length $?c_r5) 1))
           (and (> (length $?c_r3) 1) (> (length $?c_r5) 1))
           (and (> (length $?c_r3) 1) (> (length $?c_r4) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r5) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r4) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r3) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r5) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r4) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r3) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r2) 1))
        )
  )
  =>
  (bind $?basura1 (create$))
  (bind $?basura2 (create$))
  (bind $?basura3 (create$))
  (bind $?basura4 (create$))
  (bind $?basura5 (create$))
  (bind ?results 0)
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (loop-for-count (?j 1 (length $?c_r2)) do
      (bind ?b (nth$ ?j $?c_r2))
      (loop-for-count (?k 1 (length $?c_r3)) do
      	(bind ?c (nth$ ?k $?c_r3))
        (loop-for-count (?w 1 (length $?c_r4)) do
          (bind ?d (nth$ ?w $?c_r4))
          (loop-for-count (?q 1 (length $?c_r5)) do
            (bind ?e (nth$ ?q $?c_r5))
        		(if (and
                    (= ?r_v (+ ?a ?b ?c ?d ?e))
                    (neq ?a ?b)
                    (neq ?a ?c)
                    (neq ?a ?d)
                    (neq ?a ?e)
                    (neq ?b ?c)
                    (neq ?b ?d)
                    (neq ?b ?e)
                    (neq ?c ?d)
                    (neq ?c ?e)
                    (neq ?d ?e)
                )
          		then
             		(bind ?results (+ ?results +1))
                (bind ?c_candidate1 ?a)
                (if (not (member ?a $?basura1))
                   then (bind $?basura1 (create$ ?a $?basura1))
                )
                (bind ?c_candidate2 ?b)
                (if (not (member ?b $?basura2))
                   then (bind $?basura2 (create$ ?b $?basura2))
                )
                (bind ?c_candidate3 ?c)
                (if (not (member ?c $?basura3))
                   then (bind $?basura3 (create$ ?c $?basura3))
                )
                (bind ?c_candidate4 ?d)
                (if (not (member ?d $?basura4))
                   then (bind $?basura4 (create$ ?d $?basura4))
                )
                (bind ?c_candidate5 ?e)
                (if (not (member ?e $?basura5))
                   then (bind $?basura5 (create$ ?e $?basura5))
                )
            )
          )
      	)
      )
    )
  )
  (if (= ?results 1)
    then (modify ?h1 (rango ?c_candidate1))
         (modify ?h2 (rango ?c_candidate2))
         (modify ?h3 (rango ?c_candidate3))
         (modify ?h4 (rango ?c_candidate4))
         (modify ?h5 (rango ?c_candidate5))
         (printout t crlf "***** Encuentra candidado unico 5c -> " ?r_c1 "(" ?c_candidate1 "), " ?r_c2 "(" ?c_candidate2 "), " ?r_c3 "(" ?c_candidate3 "), " ?r_c4 "(" ?c_candidate4 "), " ?r_c5 "(" ?c_candidate5 ")" crlf)
  )
  (if (> ?results 1)
    then (if (< (length $?basura1) (length $?c_r1))
            then
            (assert (basura (id ?r_c1) (rango $?basura1)))
            (printout t "Recolecta basura (5c) " ?r_c1 " - " $?basura1 crlf)
         )
         (if (< (length $?basura2) (length $?c_r2))
                 then
            (assert (basura (id ?r_c2) (rango $?basura2)))
            (printout t "Recolecta basura (5c) " ?r_c2 " - " $?basura2 crlf)
         )
         (if (< (length $?basura3) (length $?c_r3))
                 then
            (assert (basura (id ?r_c3) (rango $?basura3)))
            (printout t "Recolecta basura (5c) " ?r_c3 " - " $?basura3 crlf)
         )
         (if (< (length $?basura4) (length $?c_r4))
                 then
            (assert (basura (id ?r_c4) (rango $?basura4)))
            (printout t "Recolecta basura (5c) " ?r_c4 " - " $?basura4 crlf)
         )
         (if (< (length $?basura5) (length $?c_r5))
                 then
            (assert (basura (id ?r_c5) (rango $?basura5)))
            (printout t "Recolecta basura (5c) " ?r_c5 " - " $?basura5 crlf)
         )
  )
)

;;; Búsqueda de candidatos únicos con 6c. Genera basura en caso de existir.
(defrule busca-candidato-unico-6c
  (declare (salience ?*BajaPrioidad*))
  (restriccion (valor ?r_v) (casillas ?r_c1 ?r_c2 ?r_c3 ?r_c4 ?r_c5 ?r_c6))
  ?h1 <- (celda (id ?r_c1) (rango $?c_r1))
  ?h2 <- (celda (id ?r_c2) (rango $?c_r2))
  ?h3 <- (celda (id ?r_c3) (rango $?c_r3))
  ?h4 <- (celda (id ?r_c4) (rango $?c_r4))
  ?h5 <- (celda (id ?r_c5) (rango $?c_r5))
  ?h6 <- (celda (id ?r_c6) (rango $?c_r6))
  (test (or
           (and (> (length $?c_r5) 1) (> (length $?c_r6) 1))
           (and (> (length $?c_r4) 1) (> (length $?c_r6) 1))
           (and (> (length $?c_r4) 1) (> (length $?c_r5) 1))
           (and (> (length $?c_r3) 1) (> (length $?c_r6) 1))
           (and (> (length $?c_r3) 1) (> (length $?c_r5) 1))
           (and (> (length $?c_r3) 1) (> (length $?c_r4) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r6) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r5) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r4) 1))
           (and (> (length $?c_r2) 1) (> (length $?c_r3) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r5) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r5) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r4) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r3) 1))
           (and (> (length $?c_r1) 1) (> (length $?c_r2) 1))
        )
  )
  =>
  (bind $?basura1 (create$))
  (bind $?basura2 (create$))
  (bind $?basura3 (create$))
  (bind $?basura4 (create$))
  (bind $?basura5 (create$))
  (bind $?basura6 (create$))
  (bind ?results 0)
  (loop-for-count (?i 1 (length $?c_r1)) do
    (bind ?a (nth$ ?i $?c_r1))
    (loop-for-count (?j 1 (length $?c_r2)) do
      (bind ?b (nth$ ?j $?c_r2))
      (loop-for-count (?k 1 (length $?c_r3)) do
      	(bind ?c (nth$ ?k $?c_r3))
        (loop-for-count (?w 1 (length $?c_r4)) do
          (bind ?d (nth$ ?w $?c_r4))
          (loop-for-count (?q 1 (length $?c_r5)) do
            (bind ?e (nth$ ?q $?c_r5))
            (loop-for-count (?r 1 (length $?c_r6)) do
              (bind ?f (nth$ ?r $?c_r6))
          		(if (and
                      (= ?r_v (+ ?a ?b ?c ?d ?e ?f))
                      (neq ?a ?b)
                      (neq ?a ?c)
                      (neq ?a ?d)
                      (neq ?a ?e)
                      (neq ?a ?f)
                      (neq ?b ?c)
                      (neq ?b ?d)
                      (neq ?b ?e)
                      (neq ?b ?f)
                      (neq ?c ?d)
                      (neq ?c ?e)
                      (neq ?c ?f)
                      (neq ?d ?e)
                      (neq ?d ?f)
                      (neq ?e ?f)
                  )
            		then
               		(bind ?results (+ ?results +1))
                  (bind ?c_candidate1 ?a)
                  (if (not (member ?a $?basura1))
                     then (bind $?basura1 (create$ ?a $?basura1))
                  )
                  (bind ?c_candidate2 ?b)
                  (if (not (member ?b $?basura2))
                     then (bind $?basura2 (create$ ?b $?basura2))
                  )
                  (bind ?c_candidate3 ?c)
                  (if (not (member ?c $?basura3))
                     then (bind $?basura3 (create$ ?c $?basura3))
                  )
                  (bind ?c_candidate4 ?d)
                  (if (not (member ?d $?basura4))
                     then (bind $?basura4 (create$ ?d $?basura4))
                  )
                  (bind ?c_candidate5 ?e)
                  (if (not (member ?e $?basura5))
                     then (bind $?basura5 (create$ ?e $?basura5))
                  )
                  (bind ?c_candidate6 ?f)
                  (if (not (member ?f $?basura6))
                     then (bind $?basura6 (create$ ?f $?basura6))
                  )
              )
            )
          )
      	)
      )
    )
  )
  (if (= ?results 1)
    then (modify ?h1 (rango ?c_candidate1))
         (modify ?h2 (rango ?c_candidate2))
         (modify ?h3 (rango ?c_candidate3))
         (modify ?h4 (rango ?c_candidate4))
         (modify ?h5 (rango ?c_candidate5))
         (modify ?h6 (rango ?c_candidate6))
         (printout t crlf "****** Encuentra candidado unico 6c -> " ?r_c1 "(" ?c_candidate1 "), "
                                                                    ?r_c2 "(" ?c_candidate2 "), "
                                                                    ?r_c3 "(" ?c_candidate3 "), "
                                                                    ?r_c4 "(" ?c_candidate4 "), "
                                                                    ?r_c5 "(" ?c_candidate5 "), "
                                                                    ?r_c6 "(" ?c_candidate6 ")" crlf)
  )
  (if (> ?results 1)
    then (if (< (length $?basura1) (length $?c_r1))
            then
            (assert (basura (id ?r_c1) (rango $?basura1)))
            (printout t "Recolecta basura (6c) " ?r_c1 " - " $?basura1 crlf)
         )
         (if (< (length $?basura2) (length $?c_r2))
                 then
            (assert (basura (id ?r_c2) (rango $?basura2)))
            (printout t "Recolecta basura (6c) " ?r_c2 " - " $?basura2 crlf)
         )
         (if (< (length $?basura3) (length $?c_r3))
                 then
            (assert (basura (id ?r_c3) (rango $?basura3)))
            (printout t "Recolecta basura (6c) " ?r_c3 " - " $?basura3 crlf)
         )
         (if (< (length $?basura4) (length $?c_r4))
                 then
            (assert (basura (id ?r_c4) (rango $?basura4)))
            (printout t "Recolecta basura (6c) " ?r_c4 " - " $?basura4 crlf)
         )
         (if (< (length $?basura5) (length $?c_r5))
                 then
            (assert (basura (id ?r_c5) (rango $?basura5)))
            (printout t "Recolecta basura (6c) " ?r_c5 " - " $?basura5 crlf)
         )
         (if (< (length $?basura6) (length $?c_r6))
                 then
            (assert (basura (id ?r_c6) (rango $?basura6)))
            (printout t "Recolecta basura (6c) " ?r_c6 " - " $?basura6 crlf)
         )
  )
)

;;;============================================================================
;;; Reglas para imprimir el resultado
;;;============================================================================

;;;   Las siguientes reglas permiten visualizar el estado del puzle, una vez
;;; aplicadas todas las reglas que implementan las estrategias de resolución.
;;; La prioridad de estas reglas es -10 para que sean las últimas en
;;; aplicarse.

;;;   Para las casillas del tablero con un único valor en su rango se indica
;;; dicho valor, para las casillas del tablero en las que no se haya podido
;;; deducir el valor se indica el sí­mbolo '?'. El resto de las casillas hasta
;;; completar la cuadrí­cula 9x9 se dejan en blanco.

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

;;;   Esta función crea una lista de identificadores de casillas en horizontal.

(deffunction crea-casillas-horizontal (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat ?f (+ ?c ?i))))))
  ?datos)

;;;   Esta función construye los hechos que representan las restricciones de
;;; una lí­nea horizontal del Kakuro.

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

;;;   Esta función crea una lista de identificadores de casillas en vertical.

(deffunction crea-casillas-vertical (?f ?c ?n)
  (bind ?datos (create$))
  (loop-for-count
   (?i 0 (- ?n 1))
   (bind ?datos (insert$ ?datos ?n (eval (str-cat (+ ?f ?i) ?c)))))
  ?datos)

;;;   Esta función construye los hechos que representan las restricciones de
;;; una lí­nea horizontal del Kakuro.

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

;;;   Esta función construye todos los hechos que representan las restricciones
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

;;;   Esta función localiza el Kakuro que se quiere resolver en el fichero de
;;; ejemplos.

(deffunction lee-kakuro (?n)
  (open "ejemplos.txt" data "r")
  (loop-for-count (?i 1 (- ?n 1))
                  (readline data))
  (bind ?datos (readline data))
  (procesa-restricciones-ejemplo ?datos)
  (close data))

;;;   Esta regla pregunta al usuario que número de Kakuro del fichero de
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
