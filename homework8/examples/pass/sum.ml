let x = inl 42 in
case x of
| inl y -> y + 1
| inr z -> if z then 1 else 0