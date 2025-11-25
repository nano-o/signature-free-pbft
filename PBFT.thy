theory PBFT
  imports Main "HOL-Statespace.StateSpaceSyntax"
begin

definition compatible where
  "compatible (b::'b::order) b' \<equiv> b \<le> b' \<or> b' \<le> b"

statespace ('p, 'v, 'b) vars =
  committed :: "'p \<Rightarrow> 'v::linorder \<Rightarrow> 'b::order \<Rightarrow> bool"
  prepared :: "'p \<Rightarrow>  'v \<Rightarrow> 'b \<Rightarrow> bool"
  pre_prepared :: "'p \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> bool"
  view :: "'p \<Rightarrow> 'v"

no_notation Set.member  (\<open>'(\<in>')\<close>)
no_notation Set.member  (\<open>(\<open>notation=\<open>infix \<in>\<close>\<close>_/ \<in> _)\<close> [51, 51] 50)

print_locale vars

locale pbft = vars _ _ _ _ _ _ project_HOL_bool_'b_fun_'v_fun_'p_fun
  for  project_HOL_bool_'b_fun_'v_fun_'p_fun :: "_ \<Rightarrow> 'p \<Rightarrow> 'v::linorder \<Rightarrow> 'b::order \<Rightarrow> bool" + \<comment> \<open>boilerplate to unify type variables\<close>
  fixes quorum_member :: "'p \<Rightarrow> 'q \<Rightarrow> bool" (infix "\<in>" 50)
    and byz :: "'p \<Rightarrow> bool"
  assumes "\<And> q1 q2 . \<exists> p . \<not> byz p \<and> p \<in> q1 \<and> p \<in> q2" \<comment> \<open>quorum intersection\<close>
begin

definition inv0 where
  \<comment> \<open>No correct party has pre-prepared, prepared, or committed anything after its current view\<close>
  "inv0 s \<equiv> \<forall> p v b. \<not> byz p \<longrightarrow> 
    ((s\<cdot>pre_prepared) p v b \<or> (s\<cdot>prepared) p v b \<or> (s\<cdot>committed) p v b) \<longrightarrow> 
    v \<le> (s\<cdot>view) p"

definition inv1 where
  \<comment> \<open>If a party commits a block, then a quorum has prepared it\<close>
  "inv1 s \<equiv> \<forall> p v b . \<not> byz p \<and> (s\<cdot>committed) p v b \<longrightarrow> (\<exists> q . \<forall> p' . p' \<in> q \<and> \<not> byz p' \<longrightarrow> (s\<cdot>prepared) p' v b)"

definition inv2 where
  \<comment> \<open>If a party prepares a block, then a quorum has pre-prepared it\<close>
  "inv2 s \<equiv> \<forall> p v b . \<not> byz p \<and> (s\<cdot>prepared) p v b \<longrightarrow> (\<exists> q . \<forall> p' . p' \<in> q \<and> \<not> byz p' \<longrightarrow> (s\<cdot>pre_prepared) p' v b)"

definition inv3 where
  \<comment> \<open>No honest party pre-prepares two different blocks in the same view\<close>
  "inv3 s \<equiv> \<forall> p v b b' . \<not> byz p \<and> (s\<cdot>pre_prepared) p v b \<and> (s\<cdot>pre_prepared) p v b' \<longrightarrow> b = b'"

definition safe where
  \<comment> \<open>A block b is safe in view v when no block that is incompatible or longer can be committed in any previous view. TODO: this will need to be augmented.\<close>
  "safe s b v \<equiv> (\<forall> p' v' b' . \<not> byz p' \<and> v' < v \<and> (s\<cdot>committed) p' v' b' \<longrightarrow> b' \<le> b)"

definition inv4 where
  \<comment> \<open>If a party pre-prepares a block b in view v, then b is safe in v\<close>
  "inv4 s \<equiv> \<forall> p v b . \<not> byz p \<and> (s\<cdot>pre_prepared) p v b \<longrightarrow> safe s b v"

section \<open>Specification of the algorithm\<close>

definition init where
  "init s \<equiv> \<forall> p v b .
      \<not>(s\<cdot>committed) p v b
    \<and> \<not>(s\<cdot>prepared) p v b
    \<and> \<not>(s\<cdot>pre_prepared) p v b"

definition commit where
  "commit s s' p q v b \<equiv>
      \<not> byz p
    \<and> (v = (s\<cdot>view) p)
    \<and> (\<forall> p' . p' \<in> q \<and> \<not> byz p' \<longrightarrow> (s\<cdot>prepared) p' v b)
    \<and> (\<forall> p' v' b'. v' > v \<and> \<not> byz p' \<and> (s\<cdot>pre_prepared) p' v' b' \<longrightarrow> compatible b b' \<and> (b \<le> b'))
    \<and> s' = s<committed := (s\<cdot>committed)(p := ((s\<cdot>committed) p)(v := ((s\<cdot>committed) p v)(b := True)))>"

definition prepare where
  "prepare s s' p q v b \<equiv>
      \<not> byz p
    \<and> (v = (s\<cdot>view) p)
    \<and> (\<forall> p' . p' \<in> q \<and> \<not> byz p' \<longrightarrow> (s\<cdot>pre_prepared) p' v b)
    \<and> s' = s<prepared := (s\<cdot>prepared)(p := ((s\<cdot>prepared) p)(v := ((s\<cdot>prepared) p v)(b := True)))>"

definition pre_prepare where
  \<comment> \<open>pre-prepare a safe block\<close>
  "pre_prepare s s' p v b \<equiv>
      \<not> byz p
    \<and> (v = (s\<cdot>view) p)
    \<and> safe s b v
    \<and> (\<forall> b' . \<not>((s\<cdot>pre_prepared) p v b'))
    \<and> s' = s<pre_prepared := (s\<cdot>pre_prepared)(p := ((s\<cdot>pre_prepared) p)(v := ((s\<cdot>pre_prepared) p v)(b := True)))>"

definition change_view where
  \<comment> \<open>Start a higher view\<close>
  "change_view s s' p v \<equiv>
      \<not> byz p
    \<and> (s\<cdot>view) p < v
    \<and> s' = s<view := (s\<cdot>view)(p := v)>"

definition byzantine_havoc where
  \<comment> \<open>Byzantine parties can do arbitrary state changes, but correct parties' state is preserved\<close>
  "byzantine_havoc s s' \<equiv>
    \<forall> p' v b. \<not> byz p' \<longrightarrow> 
        (s'\<cdot>committed) p' v b = (s\<cdot>committed) p' v b \<and>
        (s'\<cdot>prepared) p' v b = (s\<cdot>prepared) p' v b \<and>
        (s'\<cdot>pre_prepared) p' v b = (s\<cdot>pre_prepared) p' v b \<and>
        (s'\<cdot>view) p' = (s\<cdot>view) p'"

definition trans_rel where
  "trans_rel s s' p q v b \<equiv>
      commit s s' p q v b
    \<or> prepare s s' p q v b
    \<or> pre_prepare s s' p v b
    \<or> change_view s s' p v
    \<or> byzantine_havoc s s'"

lemma trans_rel_cases[consumes 1, case_names commit prepare pre_prepare change_view byzantine_havoc]:
  assumes "trans_rel s s' p q v b"
  obtains (commit) "commit s s' p q v b"
    | (prepare) "prepare s s' p q v b"
    | (pre_prepare) "pre_prepare s s' p v b"
    | (change_view) "change_view s s' p v"
    | (byzantine_havoc) "byzantine_havoc s s'"
  using assms unfolding trans_rel_def by blast

section \<open>Induction proofs\<close>

lemma inv0_inductive:
  shows "init s \<Longrightarrow> inv0 s" and "trans_rel s s' p q v b \<and> inv0 s \<Longrightarrow> inv0 s'"
proof -
  show "init s \<Longrightarrow> inv0 s"
    by (simp add: init_def inv0_def)
next
  show "trans_rel s s' p q v b \<and> inv0 s \<Longrightarrow> inv0 s'"
  proof -
    assume asm: "trans_rel s s' p q v b \<and> inv0 s"
    then have inv0: "inv0 s" and trans: "trans_rel s s' p q v b" by simp_all
    from trans show "inv0 s'"
    proof (cases rule: trans_rel_cases)
      case commit
      \<comment> \<open>commit doesn't change view or any pre_prepared/prepared fields\<close>
      thus ?thesis using inv0 unfolding inv0_def commit_def by auto
    next
      case prepare
      \<comment> \<open>prepare doesn't change view or any pre_prepared/committed fields\<close>
      thus ?thesis using inv0 unfolding inv0_def prepare_def by auto
    next
      case pre_prepare
      \<comment> \<open>pre_prepare doesn't change view or any prepared/committed fields\<close>
      thus ?thesis using inv0 unfolding inv0_def pre_prepare_def by auto
    next
      case change_view
      \<comment> \<open>change_view only increases view for one party, preserves all prepared/committed/pre_prepared\<close>
      thus ?thesis using inv0 unfolding inv0_def change_view_def 
        by (auto; metis order.strict_implies_order order.trans)
    next
      case byzantine_havoc
      \<comment> \<open>byzantine_havoc preserves all correct parties' state\<close>
      thus ?thesis using inv0 unfolding inv0_def byzantine_havoc_def by auto
    qed
  qed
qed

lemma inv1_inductive:
  shows "init s \<Longrightarrow> inv1 s" and "trans_rel s s' p q v b \<and> inv1 s \<Longrightarrow> inv1 s'"
proof -
  show "init s \<Longrightarrow> inv1 s"
    by (simp add: init_def inv1_def)
next
  show "trans_rel s s' p q v b \<and> inv1 s \<Longrightarrow> inv1 s'"
    unfolding trans_rel_def commit_def prepare_def pre_prepare_def change_view_def byzantine_havoc_def inv1_def
    apply auto
        apply (smt (verit) fun_upd_apply)
         apply meson+
    done
qed

lemma inv2_inductive:
  shows "init s \<Longrightarrow> inv2 s" and "trans_rel s s' p q v b \<and> inv2 s \<Longrightarrow> inv2 s'"
proof -
  show "init s \<Longrightarrow> inv2 s"
    by (simp add: init_def inv2_def)
next
  show "trans_rel s s' p q v b \<and> inv2 s \<Longrightarrow> inv2 s'"
  proof -
    assume asm: "trans_rel s s' p q v b \<and> inv2 s"
    then have inv2: "inv2 s" and trans: "trans_rel s s' p q v b" by simp_all
    from trans show "inv2 s'"
    proof (cases rule: trans_rel_cases)
      case commit
      \<comment> \<open>commit doesn't change prepared or pre_prepared\<close>
      thus ?thesis using inv2 unfolding inv2_def commit_def by auto
    next
      case prepare
      \<comment> \<open>prepare adds to prepared, doesn't change pre_prepared\<close>
      thus ?thesis using inv2 unfolding inv2_def prepare_def by auto
    next
      case pre_prepare
      \<comment> \<open>pre_prepare adds to pre_prepared, doesn't change prepared\<close>
      thus ?thesis using inv2 unfolding inv2_def pre_prepare_def 
        by (auto; metis)
    next
      case change_view
      \<comment> \<open>change_view doesn't change prepared or pre_prepared\<close>
      thus ?thesis using inv2 unfolding inv2_def change_view_def by auto
    next
      case byzantine_havoc
      \<comment> \<open>byzantine_havoc preserves all correct parties' state\<close>
      thus ?thesis using inv2 unfolding inv2_def byzantine_havoc_def by auto
    qed
  qed
qed

lemma inv3_inductive:
  shows "init s \<Longrightarrow> inv3 s" and "trans_rel s s' p q v b \<and> inv3 s \<Longrightarrow> inv3 s'"
proof -                                                              
  show "init s \<Longrightarrow> inv3 s"
    by (simp add: init_def inv3_def)
next
  show "trans_rel s s' p q v b \<and> inv3 s \<Longrightarrow> inv3 s'"
  proof -
    assume asm: "trans_rel s s' p q v b \<and> inv3 s"
    then have inv3: "inv3 s" and trans: "trans_rel s s' p q v b" by simp_all
    from trans show "inv3 s'"
    proof (cases rule: trans_rel_cases)
      case commit
      \<comment> \<open>commit doesn't change pre_prepared\<close>
      thus ?thesis using inv3 unfolding inv3_def commit_def by auto
    next
      case prepare
      \<comment> \<open>prepare doesn't change pre_prepared\<close>
      thus ?thesis using inv3 unfolding inv3_def prepare_def by auto
    next
      case pre_prepare
      \<comment> \<open>pre_prepare adds one block to pre_prepared for party p at view v, guaranteed fresh\<close>
      thus ?thesis using inv3 unfolding inv3_def pre_prepare_def by auto
    next
      case change_view
      \<comment> \<open>change_view doesn't change pre_prepared\<close>
      thus ?thesis using inv3 unfolding inv3_def change_view_def by auto
    next
      case byzantine_havoc
      \<comment> \<open>byzantine_havoc preserves all correct parties' state\<close>
      thus ?thesis using inv3 unfolding inv3_def byzantine_havoc_def by auto
    qed
  qed
qed

lemma inv4_inductive:
  shows "init s \<Longrightarrow> inv4 s" and "trans_rel s s' p q v b \<and> inv4 s \<Longrightarrow> inv4 s'"
proof -
  show "init s \<Longrightarrow> inv4 s"
    by (simp add: init_def inv4_def safe_def)
next
  show "trans_rel s s' p q v b \<and> inv4 s \<Longrightarrow> inv4 s'"
  proof -
    assume asm: "trans_rel s s' p q v b \<and> inv4 s"
    then have inv4: "inv4 s" and trans: "trans_rel s s' p q v b" by simp_all
    from trans show "inv4 s'"
    proof (cases rule: trans_rel_cases)
      case commit
      \<comment> \<open>commit doesn't change pre_prepared, but adds to committed\<close>
      \<comment> \<open>New precondition ensures compatibility with blocks pre-prepared at higher views\<close>
      thus ?thesis using inv4 unfolding inv4_def commit_def safe_def
        by auto
    next
      case prepare
      \<comment> \<open>prepare doesn't change pre_prepared or committed\<close>
      thus ?thesis using inv4 unfolding inv4_def prepare_def safe_def by auto
    next
      case pre_prepare
      \<comment> \<open>pre_prepare adds to pre_prepared, doesn't change committed\<close>
      thus ?thesis using inv4 unfolding inv4_def pre_prepare_def safe_def by auto
    next
      case change_view
      \<comment> \<open>change_view doesn't change pre_prepared or committed\<close>
      thus ?thesis using inv4 unfolding inv4_def change_view_def safe_def by auto
    next
      case byzantine_havoc
      \<comment> \<open>byzantine_havoc preserves all correct parties' state\<close>
      thus ?thesis using inv4 unfolding inv4_def byzantine_havoc_def safe_def by auto
    qed
  qed
qed

lemma l0:
  fixes s p p' v b b'
  assumes "inv2 s" and "inv3 s" 
    and "\<not> byz p" and "\<not>byz p'" 
    and "(s\<cdot>prepared) p v b" and "(s\<cdot>prepared) p' v b'"
  shows "b = b'"
proof -
  \<comment> \<open>From p's prepared message, a quorum pre-prepared b\<close>
  obtain q1 where q1: "\<forall> p1 . p1 \<in> q1 \<and> \<not> byz p1 \<longrightarrow> (s\<cdot>pre_prepared) p1 v b"
    using assms(1,3,5) unfolding inv2_def by blast
  
  \<comment> \<open>From p''s prepared message, a quorum pre-prepared b'\<close>
  obtain q2 where q2: "\<forall> p2 . p2 \<in> q2 \<and> \<not> byz p2 \<longrightarrow> (s\<cdot>pre_prepared) p2 v b'"
    using assms(1,4,6) unfolding inv2_def by blast
  
  \<comment> \<open>By quorum intersection, there's an honest party in both quorums\<close>
  obtain p'' where p'': "\<not> byz p''" "p'' \<in> q1" "p'' \<in> q2"
    using pbft_axioms unfolding pbft_def pbft_axioms_def by blast
  
  \<comment> \<open>This party pre-prepared both b and b'\<close>
  have "(s\<cdot>pre_prepared) p'' v b" using q1 p'' by blast
  moreover have "(s\<cdot>pre_prepared) p'' v b'" using q2 p'' by blast
  
  \<comment> \<open>By inv3, they must be equal\<close>
  ultimately show "b = b'"
    using assms(2) p''(1) unfolding inv3_def by blast
qed

lemma l1:
  fixes s p v b p' v' b'
  assumes "inv1 s" and "inv2 s" and "inv3 s" and "inv4 s" and "\<not> byz p" and "\<not> byz p'"
    and "(s\<cdot>committed) p v b" and "(s\<cdot>committed) p' v' b'"
  shows "compatible b b'"
proof -
  \<comment> \<open>Obtain non-Byzantine processes that prepared the blocks\<close>
  obtain p1 where p1: "\<not> byz p1" "(s\<cdot>prepared) p1 v b"
    using assms(1,5,7) pbft_axioms unfolding inv1_def pbft_def pbft_axioms_def by blast
  obtain p2 where p2: "\<not> byz p2" "(s\<cdot>prepared) p2 v' b'"
    using assms(1,6,8) pbft_axioms unfolding inv1_def pbft_def pbft_axioms_def by blast
  
  \<comment> \<open>Case analysis on the relationship between v and v'\<close>
  consider (less) "v < v'" | (equal) "v = v'" | (greater) "v' < v"
    by (metis linorder_less_linear)
  then show ?thesis
  proof cases
    case less
    \<comment> \<open>v < v': need to show b \<le> b' using safety\<close>
    \<comment> \<open>From p2's prepared message, obtain a quorum that pre-prepared b'\<close>
    obtain q where q: "\<forall> p'' . p'' \<in> q \<and> \<not> byz p'' \<longrightarrow> (s\<cdot>pre_prepared) p'' v' b'"
      using assms(2) p2 unfolding inv2_def by blast
    \<comment> \<open>By quorum intersection, there's an honest party in q\<close>
    obtain p'' where p'': "\<not> byz p''" "p'' \<in> q"
      using pbft_axioms unfolding pbft_def pbft_axioms_def by metis
    \<comment> \<open>This party pre-prepared b' at v', so by inv4, b' is safe at v'\<close>
    have "(s\<cdot>pre_prepared) p'' v' b'" using q p'' by blast
    then have "safe s b' v'" using assms(4) p''(1) unfolding inv4_def by blast
    \<comment> \<open>Since v < v' and p committed b at v, we have b \<le> b'\<close>
    then have "b \<le> b'" using less assms(5,7) unfolding safe_def by blast
    thus ?thesis unfolding compatible_def by auto
  next
    case equal
    \<comment> \<open>v = v': use l0 to show b = b'\<close>
    from p1 p2 equal have "b = b'"
      using l0[OF assms(2,3) p1(1) p2(1)] by simp
    thus ?thesis unfolding compatible_def by auto
  next
    case greater
    \<comment> \<open>v' < v: symmetric to the less case\<close>
    obtain q where q: "\<forall> p'' . p'' \<in> q \<and> \<not> byz p'' \<longrightarrow> (s\<cdot>pre_prepared) p'' v b"
      using assms(2) p1 unfolding inv2_def by blast
    obtain p'' where p'': "\<not> byz p''" "p'' \<in> q"
      using pbft_axioms unfolding pbft_def pbft_axioms_def by metis
    have "(s\<cdot>pre_prepared) p'' v b" using q p'' by blast
    then have "safe s b v" using assms(4) p''(1) unfolding inv4_def by blast
    then have "b' \<le> b" using greater assms(6,8) unfolding safe_def by blast
    thus ?thesis unfolding compatible_def by auto
  qed
qed

end