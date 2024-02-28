(*
  Authors: Albert Qiaochu Jiang
*)

theory induction_sum_odd imports
  Complex_Main
begin

theorem induction_sum_odd:
  fixes n :: nat
  assumes "n > 0"
  shows "(\<Sum>(k::nat) = 0..(n-1). 2 * k + 1) = n^2"
  using assms
proof (induct rule: nat_induct_non_zero)
  case 1
  then show ?case by simp
next
  case (Suc n)
  assume IH: "n > 0" "(\<Sum>k=0..n-1. 2*k + 1) = n\<^sup>2"
  have "(\<Sum>k=0..n. 2*k + 1) = (\<Sum>k=0..n-1. 2*k + 1) + 2*n + 1" using `n > 0`
    by (metis One_nat_def Suc.hyps(2) Suc_eq_plus1 Suc_pred add_Suc_right
        sum.atLeast0_atMost_Suc) (* TODO *)
  also have "\<dots> = n\<^sup>2 + 2*n + 1" using IH by auto
  also have "\<dots> = (n+1)\<^sup>2" by (simp add: power2_eq_square)
  ultimately show ?case by auto
qed

end