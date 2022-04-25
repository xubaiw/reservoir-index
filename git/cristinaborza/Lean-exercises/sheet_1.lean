variable ( P Q R : Prop )

theorem identity : P → P := by
  intros hP
  exact hP


example : P → Q → P := by
  intros hP hQ  
  exact hP


theorem modus_ponens : P → (P → Q) → Q := by 
  intros hP hPQ
  apply hPQ hP 


theorem tranz : (P → Q) → (Q → R) → (P → R) := by
  intros hPQ hQR hP
  apply hQR $ hPQ hP
  

example : (P → Q → R) → (P → Q) → (P → R) := by
  intros hPQR hPQ hP
  apply hPQR 
  { exact hP }
  { apply hPQ hP }



variable ( S T : Prop )

example : (P → Q) → ((P → Q) → P) → Q := by
  intros hPQ hPQP 
  apply hPQ $ hPQP hPQ


example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intros h1 h2 h3
  apply h2
  intro hQ
  apply h1
  intro hP
  exact hQ

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intros hQPP hQR hRP
  apply hQPP
  intro hQ 
  apply hRP
  apply hQR 
  exact hQ 

example : (((P → Q) → Q) → Q) → (P → Q) := by
  intros hPQQQ hP
  apply hPQQQ 
  intro hPQ
  exact hPQ $ hP

