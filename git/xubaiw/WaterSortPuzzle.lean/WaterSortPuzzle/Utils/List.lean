import Mathlib

namespace List

variable {α} [DecidableEq α] (a : α) (as bs cs : List α)

/-!
# Count 统计元素出现次数
-/

theorem count_nil : [].count a = 0 := rfl

theorem count_cons_length : as.count a = n → (a::as).count a = n + 1 := by
  induction as <;> simp_all [List.count, List.countp]

theorem count_join : ((bs ++ cs).count a) = bs.count a + cs.count a := by
  induction bs
  . simp [List.count, List.countp]
  . rename_i inst head tail ih
    by_cases h : a = head
    <;> simp_all [h, List.count, List.countp]
    <;> simp_arith

theorem length_cons_gt_zero : (a::as).length > 0 := by
  simp [List.length]
  simp_arith

theorem length_cons_lt : as.length < (a::as).length := by
  simp [List.length, List.length_cons]

theorem replicate_count : (List.replicate n a).count a = n := by
  induction n <;> simp [List.count, List.countp, List.replicate]
  assumption

end List