let app = fun f -> fun x -> f x in
let inc : int -> int = fun x -> x + 1 in
let neg = fun x -> ~ x in
(app inc 3, app neg true)