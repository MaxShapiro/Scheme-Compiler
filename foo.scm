(define stdlib-test (lambda (str len)
	(set! len (+ len 1))
	(* (- len (- len 1)) len len (* len len) (/ len len) (+ len len len) (fold-right / 1
		(map (lambda (x) (length x))
			(map (lambda (str) (fold-right (lambda (curr acc) (cons* acc curr 'char '())) '() str)) 
				(map (lambda (x) (apply string->list (list x)))
					(fold-left (lambda (acc curr) (append acc (list curr))) '()
						(map (lambda (x) (make-string len x)) (string->list str))))))))
))

(stdlib-test "helloworld" 4)
