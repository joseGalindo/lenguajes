#lang plai

;; Tipo de datos que representa la sintaxis abstracta de RCFWAEL
(define-type CFWAEL
  [num (n number?)]
  [caracter (c char?)]
  [cadena (s string?)]
  [bolean (b boolean?)]
  [es-boleano? (bol CFWAEL?)]
  [es-caracter? (cara CFWAEL?)]
  [es-lista? (eslis CFWAEL?)]
  [es-cadena? (cade CFWAEL?)]
  [id (v symbol?)]
  [binop (fun symbol?)
         (exp-izq CFWAEL?)
         (exp-der CFWAEL?)]
  [iff (con-exp CFWAEL?)
       (then-exp CFWAEL?)
       (else-exp CFWAEL?)]
  [with (arterisco boolean?)
        (vars (listof bindType?)) 
        (body CFWAEL?)]
  [fun (param-for (listof symbol?)) 
       (fun-body CFWAEL?)]
  [app (fun-exp CFWAEL?) (param-reales (listof CFWAEL?))]
  [lempty]
  [lcons (cabeza CFWAEL?) (resto CFWAEL?)]
  [lcar (lista CFWAEL?)]
  [lcdr (lista CFWAEL?)])


;; Tipo de dato que representa un valor ligado a un identificador, 
;; un Binding consiste de un id de tipo symbol y un valor de tipo FWAEL
(define-type Binding
  [bind (nombre symbol?)
        (valor CFWAEL?)]
  [bindType (nombre symbol?)
            (tipo Tipo?)
            (valor CFWAEL?)])

; Tenemos ambientes procedurales
;; Nos permite saber si una expresion es un ambiente.
;;Ambiente?: expresion -> Bool
(define Ambiente?
  (lambda (e)
    (procedure? e)))


;; Crea una funcion la cual se encarga de representar los ambientes, si
;; el nombre corresponde con el bound-name se regresa el valor, si no
;; se busca en el siguiente aSub
;; aSub: symbol -> CFWAEL-Value -> procedure -> procedure 
(define aSub
  (lambda (bound-name bound-value resto-amb)
    (lambda (nombre)
      (if (symbol=? bound-name nombre)
          bound-value
          (lookup nombre resto-amb)
          ))))

;;
(define aSubType
  (lambda (bound-name bound-type resto-amb)
    (lambda (nombre)
      (if (symbol=? bound-name nombre)
          bound-type
          (lookup nombre resto-amb)
          ))))

;; Si se encuentra el procedimiento mtSub cuando se hace lookup
;; regresa un error, ya que este ambiente es el ultimo de todos.
;; mtSub: -> error
(define mtSub
  (lambda ()
    (lambda (x) 
      (error 'lookup
             (string-append "No se encontro a:  " (symbol->string x))))
    ))


;; Tipos de datos que representan los valores de retorno de nuestro interprete
(define-type CFWAEL-Value
  [numV (n number?)]
  [boolV (b boolean?)]
  [closureV (parametros (listof symbol?))
            (cuerpo CFWAEL?)
            (env Ambiente?)]
  [exprV (expre CFWAEL?)
         (env Ambiente?)]
  [emptyV]
  [consV (cabeza CFWAEL-Value?)
          (resto CFWAEL-Value?)])


;;
;;
(define-type Tipo
  [tnumber]
  [tchar]
  [tboolean]
  [tstring]
  [tlist]
  [tlistof (t Tipo?)])

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

;;
;;
(define parsea-bindings-type
  (lambda (lista-binds)
    (map (lambda (trio)
           (bindType (car trio)
                     (parsea-tipo (caddr trio))
                     (parser (cadddr trio))))
         lista-binds)))

(define parsea-tipo
  (lambda (t)
    (case t
      [(number) (tnumber)]
      [(char) (tchar)]
      [(boolean) (tboolean)]
      [(string) (tstring)]
      )))

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
      [(char? expresion) (caracter expresion)]
      [(string? expresion) (cadena expresion)]
      [(symbol? expresion) (if (symbol=? expresion 'lempty)
                               (lempty)
                               (id expresion))]
      [(boolean? expresion) (bolean expresion)]
      [(list? expresion)
       (case (car expresion)
         [(+ - * / = < > <= >= and or string-append) (binop (car expresion)
                           (parser (cadr expresion))
                           (parser (caddr expresion)))]
         [(boolean?) (es-boleano? (parser (cadr expresion)))]
         [(char?) (es-caracter? (parser (cadr expresion)))]
         [(list?) (es-lista? (parser (cadr expresion)))]
         [(string?) (es-cadena? (parser (cadr expresion)))]
         [(fun) (fun (cadr expresion)
                     (parser (caddr expresion)))]

         [(if) (iff (parser (cadr expresion))
                                       (parser (caddr expresion))
                                       (parser (cadddr expresion)))]
         [(with) (with #f 
                       (parsea-bindings-type (cadr expresion))
                       (parser (caddr expresion)))]
         [(with*) (with #t
                       (parsea-bindings-type (cadr expresion))
                       (parser (caddr expresion)))]
         [(lempty) (lempty)]
         [(lcons) (lcons (parser (cadr expresion))
                         (parser (caddr expresion)))]
         [(lcar) (lcar (parser (cadr expresion)))]
         [(lcdr) (lcdr (parser (cadr expresion)))]
         [else (app (parser (car expresion))
                    (map parser (cdr expresion)))]
         )]
      )))


;;
;;
(define type-of
  (lambda (expres)
    (type-of-amb expres (mtSub))))

;;
;;
(define type-of-amb
  (lambda (expresion amb)
      (type-case CFWAEL expresion
        [num (n) (tnumber)]
        [caracter (c) (tchar)]
        [cadena (s) (tstring)]
        [bolean (b) (tboolean)]
        [es-boleano? (e) (interp (bolean (equal? (type-of-amb e amb) (tboolean))) amb)]
        [es-caracter? (e) (interp (bolean (equal? (type-of-amb e amb) (tchar))) amb)]
        [es-lista? (e) (interp (bolean (equal? (type-of-amb e amb) (tlist))) amb)]
        [es-cadena? (e) (interp (bolean (equal? (type-of-amb e amb) (tstring))) amb)]
        [binop (fun lizq lder) (checa-fun fun 
                                          (type-of-amb lizq amb)
                                          (type-of-amb lder amb))]
        [id (v) (lookup v amb)]
        [iff (test then else) (if (equal? (type-of-amb test amb) (tboolean))
                                  (let {[val (interp test amb)]}
                                    (if (boolV-b val)
                                        (type-of-amb then amb)
                                        (type-of-amb else amb)
                                      ))
                                  "Error: La condicion debe de ser de tipo boolean")]
        [with (ast params body) "with"]
        [else "Error en el checador de tipos"]
        )))



;;
(define checa-fun
  (lambda (f l r)
    (case f
      [(+ - * /) (if (and (equal? l (tnumber))
                    (equal? r (tnumber)))
               (tnumber)
               (string-append (string-append "Error: En " (symbol->string f)) 
                              " se esperan argumentos de tipo number"))]
      [(= < > <= >=) (if (and (equal? l (tnumber))
                    (equal? r (tnumber)))
               (tboolean)
               (string-append (string-append "Error: En " (symbol->string f)) 
                              " se esperan argumentos de tipo number"))]
      [(and or ) (if (and (equal? l (tboolean))
                    (equal? r (tboolean)))
               (tboolean)
               (string-append (string-append "Error: En " (symbol->string f)) 
                              " se esperan argumentos de tipo boolean"))]
      [(string-append) (if (and (equal? l (tstring))
                                (equal? r (tstring)))
                           (tstring)
                           (string-append (string-append "Error: En " (symbol->string f)) 
                                          " se esperan argumentos de tipo string"))]
      )))

;;
(define prueba
  (lambda (e)
    (type-of (parser e))))
;-------------------------------------------------------------------------------
;-------------------------------------------------------------------------------
;------------------------ Cosas Para Interpretar -------------------------------
;-------------------------------------------------------------------------------
;-------------------------------------------------------------------------------


;; Reduce el arbol de sintaxis abstracta a un numero, booleano o lista.
;; interp: CFWAEL -> CFWAEL-Value
(define interp
  (lambda (expr amb)
    (type-case CFWAEL expr
      [num (n) (numV n)]
      [bolean (b) (boolV b)]
      [id (v) (lookup v amb)]
      [binop (fun lizq lder) (opera-rcfwael fun 
                                          (interp lizq amb) 
                                          (interp lder amb))]
      [lempty () (emptyV)]
      [lcons (cabeza resto) (consV (interp cabeza amb)
                                    (interp resto amb))]
      [lcar (lista) (consV-cabeza (interp lista amb))] 
      [lcdr (lista) (consV-resto (interp lista amb))]
      [iff (co-exp th-exp el-exp) (if (boolV-b (interp co-exp amb))
                                      (interp th-exp amb)
                                      (interp el-exp amb))]
      [with (ast params body) (if ast
                                  (interp body (foldl (lambda (b env)
                                                        (aSub (bind-nombre b)
                                                              (interp (bind-valor b) env)
                                                              env))
                                                      amb
                                                      params))
                                  (interp body (foldl (lambda (b env)
                                                        (aSub (bind-nombre b)
                                                              (interp (bind-valor b) amb)
                                                              env))
                                                      amb
                                                      params)))]
      [fun (lst-params cuerpo) (closureV lst-params 
                                         cuerpo 
                                         amb)]
      [app (fun-expr arg-expr) (let ([val-fun (interp fun-expr amb)]
                                     [val-arg (map (lambda (a)
                                                     (interp a amb)) arg-expr)])
                                 (type-case CFWAEL-Value val-fun
                                   [closureV (params-cl cuerpo-cl amb-cl)
                                             (interp cuerpo-cl
                                                     (foldl (lambda (ls la env)
                                                              (aSub ls la env))
                                                            amb-cl
                                                            params-cl
                                                            val-arg))]
                                   [else (error 'app "no se puede interpretar")]
                                   ))]
      [else "El sistema checador de tipos se encarga de ellos"]
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