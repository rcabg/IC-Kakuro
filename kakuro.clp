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
;;; Estrategias de resoluciÃ³n
;;;============================================================================

;;;   El objetivo del trabajo consiste en implementar un conjunto de reglas
;;; CLIPS que resuelvan un Kakuro de forma deductiva, es decir, deduciendo el
;;; valor de una casilla a partir de reglas que analicen los posibles valores
;;; de las casillas relacionadas.

;;; Regla 1
;;; Eliminar los valores de las celdas mayores a los de las restricciones

(defrule elimina-mayores-a-restricciones
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
  ?h1 <- (restriccion (valor ?r_v&:(and (eq (mod ?r_v 2) 0) (<= ?r_v 18))) (casillas ?c1 ?c2))
  ?h2 <- (celda (id ?c_id&:(or (eq ?c_id ?c1) (eq ?c_id ?c2))) (rango $?c_ini ?c_r&:(eq ?c_r (div ?c_r 2)) $?c_fin))
  =>
  (modify ?h2 (rango $?c_ini $?c_fin))
  (printout t "Se activa regla 3" crlf))

;;; Regla 4: de los números comunes (restricción 2 a 2 de 17 y 16)
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
  (printout t "Se activa regla 4" crlf)
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

;;; Regla 5: completa una restriccion de 2 casillas en el que una esté resuelta
(defrule completa-2
  (celda (id ?c_c) (rango ?c_v))
  (restriccion (valor ?r_v) (casillas $?r_c_ini ?r_c $?r_c_fin))
  (test (= (+ (+ (length $?r_c_ini) (length $?r_c_fin)) 1) 2))
  (test (member ?c_c (create$ $?r_c_ini ?r_c $?r_c_fin)))
  ?h1 <- (celda (id ?r_c&~?c_c) (rango $?h1_r))
  (test (> (length $?h1_r) 1))
  =>
  (modify ?h1 (rango (- ?r_v ?c_v)))
  (printout t "Se activa regla 6 " ?r_c crlf)
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
