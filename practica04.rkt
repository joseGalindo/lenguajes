#lang plai

;; Tipo de datos que representa la sintaxis abstracta de RCFWAEL
(define-type RCFWAEL
  [num (n number?)]
  [bolean (b boolean?)]
  [id (v symbol?)]
  [binop (fun symbol?)
         (exp-izq RCFWAEL?)
         (exp-der RCFWAEL?)]
  [mif (con-exp RCFWAEL?)
       (then-exp RCFWAEL?)
       (else-exp RCFWAEL?)]
  [with (arterisco boolean?)
        (vars (listof bind?)) 
        (body RCFWAEL?)]
  [fun (param-for (listof symbol?)) 
       (fun-body RCFWAEL?)]
  [rec (params-rec (listof bind?))
    (cuerpo RCFWAEL?)]
  [app (fun-exp RCFWAEL?) (param-reales (listof RCFWAEL?))]
  [lempty]
  [lcons (cabeza RCFWAEL?) (resto RCFWAEL?)]
  [lcar (lista RCFWAEL?)]
  [lcdr (lista RCFWAEL?)]
  [ltake (numero RCFWAEL?) (lista RCFWAEL?)])


;; Tipo de dato que representa un valor ligado a un identificador, 
;; un Binding consiste de un id de tipo symbol y un valor de tipo FWAEL
(define-type Binding
  [bind (nombre symbol?)
        (valor RCFWAEL?)])

; Tenemos ambientes procedurales
;; Nos permite saber si una expresion es un ambiente.
;;Ambiente?: expresion -> Bool
(define Ambiente?
  (lambda (e)
    (procedure? e)))


;; Crea una funcion la cual se encarga de representar los ambientes, si
;; el nombre corresponde con el bound-name se regresa el valor, si no
;; se busca en el siguiente aSub
;; aSub: symbol -> RCFWAEL-Value -> procedure -> procedure 
(define aSub
  (lambda (bound-name bound-value resto-amb)
    (lambda (nombre)
      (if (symbol=? bound-name nombre)
          bound-value
          (lookup nombre resto-amb)
          ))))

;; Si se encuentra el procedimiento mtSub cuando se hace lookup
;; regresa un error, ya que este ambiente es el ultimo de todos.
;; mtSub: -> error
(define mtSub
  (lambda ()
    (lambda (x) 
      (error 'lookup
             (string-append "No se encontro " (symbol->string x))))
    ))


;; Tipos de datos que representan los valores de retorno de nuestro interprete
(define-type RCFWAEL-Value
  [numV (n number?)]
  [boolV (b boolean?)]
  [closureV (parametros (listof symbol?))
            (cuerpo RCFWAEL?)
            (env Ambiente?)]
  [exprV (expre RCFWAEL?)
         (env Ambiente?)]
  [emptyV]
  [consV (cabeza RCFWAEL-Value?)
          (resto RCFWAEL-Value?)])


;; Dada una lista de tuplas, donde cada tupla contiene un identificador
;; y un valor, regresa una lista de binding, que es la representacion en
;; nuestra sintaxis.
;; parsea-bindings: listof(B) -> listof(bind?)
(define parsea-bindings
  (lambda (lista-binds)
    (map (lambda (pareja)
           (bind (car pareja)
                 (parser (cadr pareja))))
         lista-binds)))


;; Busca una variable en el ambiente, si la encuentra regresa el valor de
;; la variable, si no sigue buscando en los otros ambientes.
;; lookup: symbol -> Ambiente -> RCFWAEL
(define lookup
  (lambda (var amb)
    (amb var)))


;; Convierte una lista de simbolos en sintaxis de nuestro interprete,
;; dependiendo de la entrada se parsea para ver que se cumplan la sintaxis.
;; parser: listof (symbol) -> RCFWAEL
(define parser
  (lambda (expresion)
    (cond
      [(number? expresion) (num expresion)]
      [(symbol? expresion) (if (symbol=? expresion 'lempty)
                               (lempty)
                               (id expresion))]
      [(boolean? expresion) (bolean expresion)]
      [(list? expresion)
       (case (car expresion)
         [(+ - * / = < > <= >= and or) (binop (car expresion)
                           (parser (cadr expresion))
                           (parser (caddr expresion)))]
         [(fun) (fun (cadr expresion)
                     (parser (caddr expresion)))]
         [(rec) (rec (parsea-bindings (cadr expresion))
                  (parser (caddr expresion)))]
         [(if) (mif (parser (cadr expresion))
                                       (parser (caddr expresion))
                                       (parser (cadddr expresion)))]
         [(with) (with #f 
                       (parsea-bindings (cadr expresion))
                       (parser (caddr expresion)))]
         [(with*) (with #t
                       (parsea-bindings (cadr expresion))
                       (parser (caddr expresion)))]
         [(lempty) (lempty)]
         [(lcons) (lcons (parser (cadr expresion))
                         (parser (caddr expresion)))]
         [(lcar) (lcar (parser (cadr expresion)))]
         [(lcdr) (lcdr (parser (cadr expresion)))]
         [(ltake) (ltake (parser (cadr expresion)) 
                         (parser (caddr expresion)))]
         [else (app (parser (car expresion))
                    (map parser (cdr expresion)))]
         )]
      )))


;; Punto Estricto evalua una exprV hasta reducirla a un valor,
;; ya sea una lista, boleano o numero.
;; punto-estricto: RCFWAEL -> RCFWAEL-Value
(define punto-estricto
  (lambda (expr)
    (type-case RCFWAEL-Value expr
      [exprV (ex am) (punto-estricto (interp ex am))]
      [else expr]
      )))

;; Reduce el arbol de sintaxis abstracta a un numero, booleano o lista.
;; interp: RCFWAEL -> RCFWAEL-Value
(define interp
  (lambda (expr amb)
    (type-case RCFWAEL expr
      [num (n) (numV n)]
      [bolean (b) (boolV b)]
      [id (v) (lookup v amb)]
      [binop (fun lizq lder) (opera-rcfwael fun 
                                          (punto-estricto (interp lizq amb)) 
                                          (punto-estricto (interp lder amb)))]
      [lempty () (emptyV)]
      [lcons (cabeza resto) (consV (exprV cabeza amb)
                                    (exprV resto amb))]
      [lcar (lista) (let {[lst-eval (punto-estricto (interp lista amb))]}
                      (type-case RCFWAEL-Value lst-eval
                        [consV (cabeza t) (punto-estricto cabeza)]
                        [else (error 'interp "Se debe de pasar una lista")]
                        ))] 
      [lcdr (lista) (let {[lst-eval (punto-estricto (interp lista amb))]}
                      (type-case RCFWAEL-Value lst-eval
                        [consV (h resto) resto]
                        [else (error 'interp "Se debe de pasar una lista")]))]
      [ltake (n-ele lista-eva) (let {[valor-n (interp n-ele amb)]
                                     [lst-eval (punto-estricto (interp lista-eva amb))]}
                                 (type-case RCFWAEL-Value lst-eval
                                   [consV (cabeza resto) 
                                          (if (= 0 (numV-n valor-n))
                                              (emptyV)
                                              (consV cabeza
                                                     (interp (ltake (num (- (numV-n valor-n) 1))
                                                                    (lcons-resto lista-eva)) amb)
                                                     ))]
                                   [else (error 'interp "No es una Lista")]
                                   ))]
      [mif (co-exp th-exp el-exp) (if (boolV-b (punto-estricto(interp co-exp amb)))
                                      (interp th-exp amb)
                                      (interp el-exp amb))]
      [with (ast params body) (if ast
                                  (interp body (foldl (lambda (b env)
                                                        (aSub (bind-nombre b)
                                                              (exprV (bind-valor b) env)
                                                              env))
                                                      amb
                                                      params))
                                  (interp body (foldl (lambda (b env)
                                                        (aSub (bind-nombre b)
                                                              (exprV (bind-valor b) amb)
                                                              env))
                                                      amb
                                                      params)))]
      [rec (definiciones uso)
      (interp uso
              (foldl (lambda (binds acu)
                       (letrec ([amb-recur (lambda (v)
                                               (if (symbol=? v (bind-nombre binds))
                                                   (exprV  (bind-valor binds) amb-recur)
                                                   (lookup v acu)))])
                         amb-recur))
                     amb
                     definiciones))]
      [fun (lst-params cuerpo) (closureV lst-params 
                                         cuerpo 
                                         amb)]
      [app (fun-expr arg-expr) (let ([val-fun (punto-estricto (interp fun-expr amb))]
                                     [val-arg (map (lambda (a)
                                                     (exprV a amb)) arg-expr)])
                                 (type-case RCFWAEL-Value val-fun
                                   [closureV (params-cl cuerpo-cl amb-cl)
                                             (interp cuerpo-cl
                                                     (foldl (lambda (ls la env)
                                                              (aSub ls la env))
                                                            amb-cl
                                                            params-cl
                                                            val-arg))]
                                   [else (error 'app "no se puede interpretar")]
                                   ))]
      )))

;; Dado un simbolo que representa una funcion, aplica esa funcion
;; a dos expresiones, devolviendo un valor boleano o numerico.
;; opera-rcfwael: symbol-> RCFWAEL -> RCFWAEL -> RCFWAEL-Value
(define opera-rcfwael
  (lambda (f i d)
    (case f
      [(+) (numV (+ (numV-n i)
                    (numV-n d)))]
      [(-) (numV (- (numV-n i)
                    (numV-n d)))]
      [(*) (numV (* (numV-n i)
                    (numV-n d)))]
      [(/) (if (not (= 0 (numV-n d))) 
               (numV (/ (numV-n i)
                        (numV-n d)))
               (error 'interp "No se puede dividir por 0"))]
      [(=) (boolV (= (numV-n i)
                     (numV-n d)))]
      [(<) (boolV (< (numV-n i)
                     (numV-n d)))]
      [(>) (boolV (> (numV-n i)
                     (numV-n d)))]
      [(<=) (boolV (<= (numV-n i)
                       (numV-n d)))]
      [(>=) (boolV (>= (numV-n i)
                       (numV-n d)))]
      [(and) (boolV (and (boolV-b i)
                         (boolV-b d)))]
      [(or) (boolV (or (boolV-b i)
                       (boolV-b d)))]
    )))