theory PBFT
  imports Main "HOL-Statespace.StateSpaceSyntax"
begin

definition compatible where
  "compatible (b::'b::order) b' \<equiv> b \<le> b' \<or> b' \<le> b"

statespace ('p, 'v, 'b) vars =
  committed :: "'p \<Rightarrow> 'v::linorder \<Rightarrow> 'b::order \<Rightarrow> bool"
  commit_msg :: "'p \<Rightarrow>  'v::linorder \<Rightarrow> 'b::order \<Rightarrow> bool"

no_notation Set.member  (\<open>'(\<in>')\<close>)
no_notation Set.member  (\<open>(\<open>notation=\<open>infix \<in>\<close>\<close>_/ \<in> _)\<close> [51, 51] 50)

locale pbft = vars _ _ project_HOL_bool_'b_fun_'v_fun_'p_fun
  for  project_HOL_bool_'b_fun_'v_fun_'p_fun :: "_ \<Rightarrow> 'p \<Rightarrow> 'v::linorder \<Rightarrow> 'b::order \<Rightarrow> bool" + \<comment> \<open>boilerplate to unify type variables\<close>
  fixes quorum_member :: "'p \<Rightarrow> 'q \<Rightarrow> bool" (infix "\<in>" 50)
    and byz :: "'p \<Rightarrow> bool"
  assumes "\<And> q1 q2 . \<exists> p . \<not> byz p \<and> p \<in> q1 \<and> p \<in> q2" \<comment> \<open>quorum intersection\<close>
begin

definition inv1 where
  "inv1 s \<equiv> \<forall> p v b . \<not> byz p \<and> (s\<cdot>committed) p v b \<longrightarrow> (\<exists> q . \<forall> p' . p' \<in> q \<and> \<not> byz p' \<longrightarrow> (s\<cdot>commit_msg) p' v b)"

definition inv2 where
  "inv2 s \<equiv> \<forall> p v b . \<not> byz p \<and> (s\<cdot>commit_msg) p v b \<longrightarrow> (\<forall> p' v' b' . \<not> byz p' \<and> v' < v \<and> (s\<cdot>committed) p' v' b' \<longrightarrow> b' \<le> b)"

definition inv3 where
  "inv3 s \<equiv> \<forall> p p' v b b' . \<not> byz p \<and> \<not> byz p' \<and> (s\<cdot>commit_msg) p v b \<and> (s\<cdot>commit_msg) p' v b' \<longrightarrow> b = b'"

lemma l1:
  fixes s p v b p' v' b'
  assumes "inv1 s" and "inv2 s" and "inv3 s" and "\<not> byz p" and "\<not> byz p'"
    and "(s\<cdot>committed) p v b" and "(s\<cdot>committed) p' v' b'"
  shows "compatible b b'"
proof -
  \<comment> \<open>Obtain non-Byzantine processes that sent commit messages\<close>
  obtain p1 where p1: "\<not> byz p1" "(s\<cdot>commit_msg) p1 v b"
    using assms(1,4,6) pbft_axioms unfolding inv1_def pbft_def pbft_axioms_def by blast
  obtain p2 where p2: "\<not> byz p2" "(s\<cdot>commit_msg) p2 v' b'"
    using assms(1,5,7) pbft_axioms unfolding inv1_def pbft_def pbft_axioms_def by blast
  
  \<comment> \<open>Case analysis on the relationship between v and v'\<close>
  consider (less) "v < v'" | (equal) "v = v'" | (greater) "v' < v"
    by (metis linorder_less_linear)
  then show ?thesis
  proof cases
    case less
    \<comment> \<open>v < v': use inv2 with p2's commit_msg and p's commitment\<close>
    from p2(1) p2(2) assms(4) less assms(6) have "b \<le> b'"
      using assms(2) unfolding inv2_def by blast
    thus ?thesis unfolding compatible_def by auto
  next
    case equal
    \<comment> \<open>v = v': use inv3 to show b = b'\<close>
    from p1 p2 equal have "b = b'"
      using assms(3) unfolding inv3_def by blast
    thus ?thesis unfolding compatible_def by auto
  next
    case greater
    \<comment> \<open>v' < v: use inv2 with p1's commit_msg and p''s commitment\<close>
    from p1(1) p1(2) assms(5) greater assms(7) have "b' \<le> b"
      using assms(2) unfolding inv2_def by blast
    thus ?thesis unfolding compatible_def by auto
  qed
qed

end