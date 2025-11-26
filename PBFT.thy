theory PBFT
  imports Main "HOL-Statespace.StateSpaceSyntax" "HOL-Eisbach.Eisbach"
begin

definition compatible where
  "compatible (b::'b::order) b' \<equiv> b \<le> b' \<or> b' \<le> b"

statespace ('p, 'v, 'b) vars =
  committed :: "'p \<Rightarrow> 'v::wellorder \<Rightarrow> 'b::order \<Rightarrow> bool"
  prepared :: "'p \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> bool"
  pre_prepared :: "'p \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> bool"
  view :: "'p \<Rightarrow> 'v"

no_notation Set.member  (\<open>'(\<in>')\<close>)
no_notation Set.member  (\<open>(\<open>notation=\<open>infix \<in>\<close>\<close>_/ \<in> _)\<close> [51, 51] 50)

print_locale vars

locale pbft = vars _ _ _ _ _ _ project_HOL_bool_'b_fun_'v_fun_'p_fun
  for  project_HOL_bool_'b_fun_'v_fun_'p_fun :: "_ \<Rightarrow> 'p \<Rightarrow> 'v::wellorder \<Rightarrow> 'b::order \<Rightarrow> bool" + \<comment> \<open>boilerplate to unify type variables\<close>
  fixes quorum_member :: "'p \<Rightarrow> 'q \<Rightarrow> bool" (infix "\<in>" 50)
    and byz :: "'p \<Rightarrow> bool"
  assumes quorum_intersection:"\<And> q1 q2 . \<exists> p . \<not> byz p \<and> p \<in> q1 \<and> p \<in> q2" \<comment> \<open>quorum intersection\<close>
begin

definition inv0 where
  \<comment> \<open>No correct party has pre-prepared, prepared, or committed anything after its current view\<close>
  "inv0 s \<equiv> \<forall> p v b. \<not> byz p \<longrightarrow> 
    ((s\<cdot>pre_prepared) p v b \<or> (s\<cdot>prepared) p v b \<or> (s\<cdot>committed) p v b) \<longrightarrow> 
    v \<le> (s\<cdot>view) p"

definition inv1 where
  \<comment> \<open>If a correct party commits a block, then a quorum has prepared it\<close>
  "inv1 s \<equiv> \<forall> p v b . \<not> byz p \<and> (s\<cdot>committed) p v b \<longrightarrow> (\<exists> q . \<forall> p' . p' \<in> q \<and> \<not> byz p' \<longrightarrow> (s\<cdot>prepared) p' v b)"

definition inv2 where
  \<comment> \<open>If a correct party prepares a block, then a quorum has pre-prepared it\<close>
  "inv2 s \<equiv> \<forall> p v b . \<not> byz p \<and> (s\<cdot>prepared) p v b \<longrightarrow> (\<exists> q . \<forall> p' . p' \<in> q \<and> \<not> byz p' \<longrightarrow> (s\<cdot>pre_prepared) p' v b)"

definition inv3 where
  \<comment> \<open>An correct party only pre-prepares one block per view\<close>
  "inv3 s \<equiv> \<forall> p v b b' . \<not> byz p \<and> (s\<cdot>pre_prepared) p v b \<and> (s\<cdot>pre_prepared) p v b' \<longrightarrow> b = b'"

definition safe where
  \<comment> \<open>This definition implies that a no block that is incompatible or longer than b can ever be committed in views preceding v, and only b can be committed in view v.\<close>
  "safe s b v \<equiv> \<exists> v' . v' < v
    \<and> (\<exists> q . \<forall> p . p \<in> q \<and> \<not> byz p \<longrightarrow>
          (s\<cdot>view) p \<ge> v
        \<and> (\<forall> v'' b'' . v' < v'' \<and> v'' < v \<longrightarrow> \<not>(s\<cdot>prepared) p v'' b'')
        \<and> (\<forall> b' . b' \<noteq> b \<longrightarrow> \<not> (s\<cdot>pre_prepared) p v' b'))
    \<and> (\<exists> p . \<not> byz p \<and> (s\<cdot>pre_prepared) p v' b)"

definition inv4 where
  \<comment> \<open>If a party pre-prepares a block b in view v, then b is safe in v\<close>
  "inv4 s \<equiv> \<forall> p v b . \<not> byz p \<and> (s\<cdot>pre_prepared) p v b \<longrightarrow> safe s b v"

definition inv5 where
  \<comment> \<open>No two honest parties prepare different blocks in the same view\<close>
  "inv5 s \<equiv> \<forall> p p' v b b' . \<not> byz p \<and> \<not> byz p' \<and> (s\<cdot>prepared) p v b \<and> (s\<cdot>prepared) p' v b' \<longrightarrow> b = b'"

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
    \<and> s' = s<committed := (s\<cdot>committed)(p := ((s\<cdot>committed) p)(v := ((s\<cdot>committed) p v)(b := True)))>"

definition pre_prepare where
  \<comment> \<open>pre-prepare a safe block\<close>
  "pre_prepare s s' p v b \<equiv>
      \<not> byz p
    \<and> (v = (s\<cdot>view) p)
    \<and> safe s b v
    \<and> (\<forall> b' . \<not>((s\<cdot>pre_prepared) p v b'))
    \<and> s' = s<pre_prepared := (s\<cdot>pre_prepared)(p := ((s\<cdot>pre_prepared) p)(v := ((s\<cdot>pre_prepared) p v)(b := True)))>"

definition prepare where
  "prepare s s' p q v b \<equiv>
      \<not> byz p
    \<and> (v = (s\<cdot>view) p)
    \<and> (\<forall> p' . p' \<in> q \<and> \<not> byz p' \<longrightarrow> (s\<cdot>pre_prepared) p' v b)
    \<and> s' = s<prepared := (s\<cdot>prepared)(p := ((s\<cdot>prepared) p)(v := ((s\<cdot>prepared) p v)(b := True)))>"

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

section \<open>Eisbach VCG Methods\<close>

text \<open>
  Verification condition generator methods for invariance proofs.
  These methods automate the common pattern of proving that invariants
  are preserved by transitions.
\<close>

named_theorems trans_defs
declare commit_def[trans_defs]
declare prepare_def[trans_defs]
declare pre_prepare_def[trans_defs]
declare change_view_def[trans_defs]
declare byzantine_havoc_def[trans_defs]

text \<open>
  Function update lemmas for VCG.
  fun_upd_apply is already a default simp rule, but we add related rules
  and configure auto to split on conditionals from function updates.
\<close>

text \<open>Method 1: Unfold everything and apply auto (good for simple invariants)\<close>
method invariance_vcg_auto uses inv_def = 
  (unfold trans_rel_def trans_defs inv_def, 
   auto split: if_splits)

text \<open>Method 2: Structured case split with automatic solving\<close>
method invariance_vcg_cases uses inv_def = 
  (cases rule: trans_rel_cases; auto simp: inv_def trans_defs)

text \<open>Method 3: Structured case split, leaving subgoals for manual proof\<close>
method invariance_vcg_split = 
  (cases rule: trans_rel_cases)

text \<open>Helper method to prove initialization\<close>
method prove_init uses inv_def = 
  (simp add: init_def inv_def)

section \<open>Induction proofs\<close>

lemma inv0_inductive:
  shows "init s \<Longrightarrow> inv0 s" and "trans_rel s s' p q v b \<and> inv0 s \<Longrightarrow> inv0 s'"
proof -
  show "init s \<Longrightarrow> inv0 s"
    by (prove_init inv_def: inv0_def)
next
  show "trans_rel s s' p q v b \<and> inv0 s \<Longrightarrow> inv0 s'"
    apply (invariance_vcg_auto inv_def: inv0_def)
      apply fastforce+
    done
qed

lemma inv1_inductive:
  shows "init s \<Longrightarrow> inv1 s" and "trans_rel s s' p q v b \<and> inv1 s \<Longrightarrow> inv1 s'"
proof -
  show "init s \<Longrightarrow> inv1 s"
    by (prove_init inv_def: inv1_def)
next
  show "trans_rel s s' p q v b \<and> inv1 s \<Longrightarrow> inv1 s'"
    apply (invariance_vcg_auto inv_def: inv1_def)
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
    apply (invariance_vcg_auto inv_def: inv2_def)
        apply meson+
    done
qed

lemma inv3_inductive:
  shows "init s \<Longrightarrow> inv3 s" and "trans_rel s s' p q v b \<and> inv3 s \<Longrightarrow> inv3 s'"
proof -                                                              
  show "init s \<Longrightarrow> inv3 s"
    by (simp add: init_def inv3_def)
next
  show "trans_rel s s' p q v b \<and> inv3 s \<Longrightarrow> inv3 s'"
    by (invariance_vcg_auto inv_def: inv3_def)
qed

lemma safe_sanity_check_2:
  assumes "safe s b v" and "trans_rel s s' p q v' b'"
  shows "safe s' b v"
proof -
  from \<open>safe s b v\<close> obtain v_wit q_wit where
    v_wit_lt: "v_wit < v" and
    q_wit: "\<forall> pa . pa \<in> q_wit \<and> \<not> byz pa \<longrightarrow>
          (s\<cdot>view) pa \<ge> v
        \<and> (\<forall> v'' b'' . v_wit < v'' \<and> v'' < v \<longrightarrow> \<not>(s\<cdot>prepared) pa v'' b'')
        \<and> (\<forall> bc . bc \<noteq> b \<longrightarrow> \<not> (s\<cdot>pre_prepared) pa v_wit bc)" and
    witness_exists: "\<exists> pa . \<not> byz pa \<and> (s\<cdot>pre_prepared) pa v_wit b"
    unfolding safe_def by auto
  
  from \<open>trans_rel s s' p q v' b'\<close> show "safe s' b v"
  proof (cases rule: trans_rel_cases)
    case commit
    thus ?thesis using v_wit_lt q_wit witness_exists 
      unfolding safe_def commit_def by auto
  next
    case prepare
    thus ?thesis using v_wit_lt q_wit witness_exists
      unfolding safe_def prepare_def
      by (auto; smt (verit, del_insts) leD)
  next
    case pre_prepare
    have 
      q_wit': "\<forall> pa . pa \<in> q_wit \<and> \<not> byz pa \<longrightarrow>
          (s'\<cdot>view) pa \<ge> v
        \<and> (\<forall> v'' b'' . v_wit < v'' \<and> v'' < v \<longrightarrow> \<not>(s'\<cdot>prepared) pa v'' b'')
        \<and> (\<forall> bc . bc \<noteq> b \<longrightarrow> \<not> (s'\<cdot>pre_prepared) pa v_wit bc)" 
      using v_wit_lt q_wit witness_exists pre_prepare
      unfolding safe_def pre_prepare_def by auto 
    have witness_exists': "\<exists> pa . \<not> byz pa \<and> (s'\<cdot>pre_prepared) pa v_wit b" 
      using v_wit_lt q_wit witness_exists pre_prepare
      unfolding safe_def pre_prepare_def by auto 
    show ?thesis
      using q_wit' safe_def v_wit_lt witness_exists'
      by blast
  next
    case change_view
    thus ?thesis using v_wit_lt q_wit witness_exists
      unfolding safe_def change_view_def
      by (auto; smt (verit) nless_le order_trans) 
  next
    case byzantine_havoc
    thus ?thesis using v_wit_lt q_wit witness_exists
      unfolding safe_def byzantine_havoc_def by force
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
      show ?thesis unfolding inv4_def
      proof (intro allI impI)
        fix pa va ba
        assume "\<not> byz pa \<and> (s'\<cdot>pre_prepared) pa va ba"
        then have "\<not> byz pa" and "(s\<cdot>pre_prepared) pa va ba"
          using prepare unfolding prepare_def by auto
        from \<open>inv4 s\<close> \<open>\<not> byz pa\<close> \<open>(s\<cdot>pre_prepared) pa va ba\<close> have "safe s ba va"
          unfolding inv4_def by blast
        with prepare show "safe s' ba va"
          using safe_sanity_check_2[of s ba va s' p q v b] 
          unfolding trans_rel_def by blast
      qed
    next
      case pre_prepare
      \<comment> \<open>pre_prepare adds to pre_prepared with safe precondition\<close>
      show ?thesis unfolding inv4_def
      proof (intro allI impI)
        fix pa va ba
        assume "\<not> byz pa \<and> (s'\<cdot>pre_prepared) pa va ba"
        then have pa_correct: "\<not> byz pa" by blast
        from \<open>\<not> byz pa \<and> (s'\<cdot>pre_prepared) pa va ba\<close> pre_prepare 
        have pre_in_s': "(s'\<cdot>pre_prepared) pa va ba" by blast
        show "safe s' ba va"
        proof (cases "pa = p \<and> va = v \<and> ba = b")
          case True
          \<comment> \<open>Newly pre-prepared block, safe by precondition\<close>
          from pre_prepare have "safe s b v" unfolding pre_prepare_def by blast
          with True show ?thesis 
            using safe_sanity_check_2[of s ba va s' p q v b] pre_prepare
            unfolding trans_rel_def by blast
        next
          case False
          \<comment> \<open>Already pre-prepared in s, inv4 s gives safety\<close>
          from False pre_in_s' pre_prepare have "(s\<cdot>pre_prepared) pa va ba"
            unfolding pre_prepare_def by (auto split: if_splits)
          from \<open>inv4 s\<close> pa_correct this have "safe s ba va"
            unfolding inv4_def by blast
          thus ?thesis 
            using safe_sanity_check_2[of s ba va s' p q v b] pre_prepare
            unfolding trans_rel_def by blast
        qed
      qed
    next
      case change_view
      \<comment> \<open>change_view doesn't change pre_prepared or committed\<close>
      show ?thesis unfolding inv4_def
      proof (intro allI impI)
        fix pa va ba
        assume "\<not> byz pa \<and> (s'\<cdot>pre_prepared) pa va ba"
        then have "\<not> byz pa" and "(s\<cdot>pre_prepared) pa va ba"
          using change_view unfolding change_view_def by auto
        from \<open>inv4 s\<close> \<open>\<not> byz pa\<close> \<open>(s\<cdot>pre_prepared) pa va ba\<close> have "safe s ba va"
          unfolding inv4_def by blast
        with change_view show "safe s' ba va"
          using safe_sanity_check_2[of s ba va s' p q v b] 
          unfolding trans_rel_def by blast
      qed
    next
      case byzantine_havoc
      \<comment> \<open>byzantine_havoc preserves all correct parties' state\<close>
      show ?thesis unfolding inv4_def
      proof (intro allI impI)
        fix pa va ba
        assume "\<not> byz pa \<and> (s'\<cdot>pre_prepared) pa va ba"
        then have "\<not> byz pa" and "(s\<cdot>pre_prepared) pa va ba"
          using byzantine_havoc unfolding byzantine_havoc_def by auto
        from \<open>inv4 s\<close> \<open>\<not> byz pa\<close> \<open>(s\<cdot>pre_prepared) pa va ba\<close> have "safe s ba va"
          unfolding inv4_def by blast
        with byzantine_havoc show "safe s' ba va"
          using safe_sanity_check_2[of s ba va s' p q v b] 
          unfolding trans_rel_def by blast
      qed
    qed
  qed
qed

lemma prepare_blocks_equal:
  assumes "\<not> byz p'" "(s\<cdot>prepared) p' v b'" 
    and "\<forall> p'' . p'' \<in> q \<and> \<not> byz p'' \<longrightarrow> (s\<cdot>pre_prepared) p'' v b"
    and "inv2 s" "inv3 s"
  shows "b = b'"
proof -
  from assms(1,2,4) obtain q' where
    "\<forall> p'' . p'' \<in> q' \<and> \<not> byz p'' \<longrightarrow> (s\<cdot>pre_prepared) p'' v b'"
    unfolding inv2_def by blast
  obtain p'' where "\<not> byz p''" "p'' \<in> q" "p'' \<in> q'"
    using quorum_intersection by blast
  with assms(3) have "(s\<cdot>pre_prepared) p'' v b" by blast
  from \<open>\<forall> p'' . p'' \<in> q' \<and> \<not> byz p'' \<longrightarrow> (s\<cdot>pre_prepared) p'' v b'\<close> \<open>\<not> byz p''\<close> \<open>p'' \<in> q'\<close>
  have "(s\<cdot>pre_prepared) p'' v b'" by blast
  from assms(5) \<open>\<not> byz p''\<close> \<open>(s\<cdot>pre_prepared) p'' v b\<close> \<open>(s\<cdot>pre_prepared) p'' v b'\<close>
  show "b = b'" unfolding inv3_def by blast
qed

lemma safe_not_contradicted:
  assumes "safe s b v" and "v' < v" and "(s\<cdot>committed) p v' b'"
    and "\<not> byz p"
    and "inv1 s" and "inv2 s" and "inv3 s" and "inv4 s"
  shows "b' \<le> b"
using assms
proof (induction v arbitrary: b p rule: less_induct)
  case (less v)
  \<comment> \<open>Extract witnesses from safe definition\<close>
  from \<open>safe s b v\<close> obtain v_wit q where
    v_wit_less: "v_wit < v" and
    q_safe: "\<forall>pa. pa \<in> q \<and> \<not> byz pa \<longrightarrow> 
        (s\<cdot>view) pa \<ge> v 
      \<and> (\<forall>v'' b''. v_wit < v'' \<and> v'' < v \<longrightarrow> \<not>(s\<cdot>prepared) pa v'' b'')
      \<and> (\<forall>b'. b' \<noteq> b \<longrightarrow> \<not>(s\<cdot>pre_prepared) pa v_wit b')" and
    witness_b: "\<exists> pa . \<not> byz pa \<and> (s\<cdot>pre_prepared) pa v_wit b"
    unfolding safe_def by auto
  
  \<comment> \<open>From inv1, get quorum q_prep that prepared b' at v'\<close>
  from \<open>\<not> byz p\<close> \<open>(s\<cdot>committed) p v' b'\<close> \<open>inv1 s\<close>
  obtain q_prep where q_prep: "\<forall>pa. pa \<in> q_prep \<and> \<not> byz pa \<longrightarrow> (s\<cdot>prepared) pa v' b'"
    unfolding inv1_def by blast
  
  \<comment> \<open>Case split on relationship between v' and v_wit\<close>
  consider (before) "v' < v_wit" | (at) "v' = v_wit" | (between) "v_wit < v' \<and> v' < v"
    using \<open>v' < v\<close> v_wit_less by force
  then show ?case
  proof cases
    case before
    \<comment> \<open>v' < v_wit: Get witness party and use induction hypothesis\<close>
    from witness_b obtain p_wit where
      p_wit_props: "\<not> byz p_wit" "(s\<cdot>pre_prepared) p_wit v_wit b"
      by blast
    
    \<comment> \<open>From inv4, b is safe at v_wit\<close>
    from p_wit_props \<open>inv4 s\<close> have "safe s b v_wit"
      unfolding inv4_def by blast
    
    \<comment> \<open>Use induction hypothesis to get b' \<le> b\<close>
    from less.IH[OF v_wit_less this before \<open>(s\<cdot>committed) p v' b'\<close> \<open>\<not> byz p\<close> \<open>inv1 s\<close> \<open>inv2 s\<close> \<open>inv3 s\<close> \<open>inv4 s\<close>]
    show ?thesis .
  next
    case at
    \<comment> \<open>v' = v_wit: use inv2 to get quorum that pre-prepared b', then quorum intersection\<close>
    \<comment> \<open>Pick any party from q_prep that prepared b'\<close>
    obtain p_prep where p_prep_props: "p_prep \<in> q_prep" "\<not> byz p_prep" "(s\<cdot>prepared) p_prep v' b'"
      using q_prep by (metis quorum_intersection)
    \<comment> \<open>From inv2, get quorum that pre-prepared b'\<close>
    from p_prep_props(2,3) \<open>inv2 s\<close> obtain q_pre where
      q_pre: "\<forall>pa. pa \<in> q_pre \<and> \<not> byz pa \<longrightarrow> (s\<cdot>pre_prepared) pa v' b'"
      unfolding inv2_def by blast
    \<comment> \<open>By quorum intersection, find honest party in both q and q_pre\<close>
    obtain p'' where p''_props: "\<not> byz p''" "p'' \<in> q" "p'' \<in> q_pre"
      using quorum_intersection by blast
    \<comment> \<open>This party pre-prepared b' at v' = v_wit\<close>
    from p''_props(1,3) q_pre have "(s\<cdot>pre_prepared) p'' v' b'" by blast
    with at have "(s\<cdot>pre_prepared) p'' v_wit b'" by simp
    \<comment> \<open>But q_safe says p'' hasn't pre-prepared anything \<noteq> b at v_wit\<close>
    from p''_props(1,2) q_safe have "\<forall>b'. b' \<noteq> b \<longrightarrow> \<not>(s\<cdot>pre_prepared) p'' v_wit b'" by blast
    \<comment> \<open>Therefore b' = b\<close>
    with \<open>(s\<cdot>pre_prepared) p'' v_wit b'\<close> have "b' = b" by blast
    thus ?thesis by simp
  next
    case between 
    \<comment> \<open>v_wit < v' < v: contradiction - quorum q forbids preparing in this range\<close>
    obtain p'' where "\<not> byz p''" "p'' \<in> q" "p'' \<in> q_prep"
      using quorum_intersection by blast
    with q_safe between have "\<not>(s\<cdot>prepared) p'' v' b'" by blast
    moreover from \<open>p'' \<in> q_prep\<close> \<open>\<not> byz p''\<close> q_prep have "(s\<cdot>prepared) p'' v' b'"
      by blast
    ultimately show ?thesis by blast
  qed
qed

lemma committed_blocks_compatible:
  assumes "(s\<cdot>committed) p1 v1 b1" "\<not> byz p1"
      and "(s\<cdot>committed) p2 v2 b2" "\<not> byz p2"
      and "inv1 s" "inv2 s" "inv3 s" "inv4 s"
  shows "compatible b1 b2"
proof -
  \<comment> \<open>Case split on relationship between v1 and v2\<close>
  consider (v1_lt_v2) "v1 < v2" | (v1_eq_v2) "v1 = v2" | (v2_lt_v1) "v2 < v1"
    by force
  then show ?thesis
  proof cases
    case v1_lt_v2
    \<comment> \<open>v1 < v2: Show b1 \<le> b2\<close>
    \<comment> \<open>From inv4, there exists an honest party that pre-prepared b2, so b2 is safe at v2\<close>
    from \<open>(s\<cdot>committed) p2 v2 b2\<close> \<open>\<not> byz p2\<close> \<open>inv1 s\<close> obtain q_prep where
      q_prep: "\<forall>p. p \<in> q_prep \<and> \<not> byz p \<longrightarrow> (s\<cdot>prepared) p v2 b2"
      unfolding inv1_def by blast
    obtain p_prep where "p_prep \<in> q_prep" "\<not> byz p_prep" "(s\<cdot>prepared) p_prep v2 b2"
      using q_prep by (metis quorum_intersection)
    from \<open>\<not> byz p_prep\<close> \<open>(s\<cdot>prepared) p_prep v2 b2\<close> \<open>inv2 s\<close> obtain q_pre where
      q_pre: "\<forall>p. p \<in> q_pre \<and> \<not> byz p \<longrightarrow> (s\<cdot>pre_prepared) p v2 b2"
      unfolding inv2_def by blast
    obtain p_pre where "p_pre \<in> q_pre" "\<not> byz p_pre" "(s\<cdot>pre_prepared) p_pre v2 b2"
      using q_pre by (metis quorum_intersection)
    from \<open>\<not> byz p_pre\<close> \<open>(s\<cdot>pre_prepared) p_pre v2 b2\<close> \<open>inv4 s\<close> have "safe s b2 v2"
      unfolding inv4_def by blast
    \<comment> \<open>Use safe_not_contradicted to get b1 \<le> b2\<close>
    from safe_not_contradicted[OF this v1_lt_v2 \<open>(s\<cdot>committed) p1 v1 b1\<close> \<open>\<not> byz p1\<close> \<open>inv1 s\<close> \<open>inv2 s\<close> \<open>inv3 s\<close> \<open>inv4 s\<close>]
    have "b1 \<le> b2" .
    thus ?thesis unfolding compatible_def by simp
  next
    case v1_eq_v2
    \<comment> \<open>v1 = v2: Show b1 = b2 using inv3\<close>
    \<comment> \<open>Get quorums that prepared both blocks\<close>
    from \<open>(s\<cdot>committed) p1 v1 b1\<close> \<open>\<not> byz p1\<close> \<open>inv1 s\<close> obtain q1_prep where
      q1_prep: "\<forall>p. p \<in> q1_prep \<and> \<not> byz p \<longrightarrow> (s\<cdot>prepared) p v1 b1"
      unfolding inv1_def by blast
    from \<open>(s\<cdot>committed) p2 v2 b2\<close> \<open>\<not> byz p2\<close> \<open>inv1 s\<close> obtain q2_prep where
      q2_prep: "\<forall>p. p \<in> q2_prep \<and> \<not> byz p \<longrightarrow> (s\<cdot>prepared) p v2 b2"
      unfolding inv1_def by blast
    \<comment> \<open>Get quorums that pre-prepared both blocks\<close>
    obtain p1_prep where "p1_prep \<in> q1_prep" "\<not> byz p1_prep" "(s\<cdot>prepared) p1_prep v1 b1"
      using q1_prep by (metis quorum_intersection)
    from \<open>\<not> byz p1_prep\<close> \<open>(s\<cdot>prepared) p1_prep v1 b1\<close> \<open>inv2 s\<close> obtain q1_pre where
      q1_pre: "\<forall>p. p \<in> q1_pre \<and> \<not> byz p \<longrightarrow> (s\<cdot>pre_prepared) p v1 b1"
      unfolding inv2_def by blast
    obtain p2_prep where "p2_prep \<in> q2_prep" "\<not> byz p2_prep" "(s\<cdot>prepared) p2_prep v2 b2"
      using q2_prep by (metis quorum_intersection)
    from \<open>\<not> byz p2_prep\<close> \<open>(s\<cdot>prepared) p2_prep v2 b2\<close> \<open>inv2 s\<close> obtain q2_pre where
      q2_pre: "\<forall>p. p \<in> q2_pre \<and> \<not> byz p \<longrightarrow> (s\<cdot>pre_prepared) p v2 b2"
      unfolding inv2_def by blast
    \<comment> \<open>By quorum intersection, find honest party in both pre-prepare quorums\<close>
    obtain p'' where "\<not> byz p''" "p'' \<in> q1_pre" "p'' \<in> q2_pre"
      using quorum_intersection by blast
    from \<open>p'' \<in> q1_pre\<close> \<open>\<not> byz p''\<close> q1_pre have "(s\<cdot>pre_prepared) p'' v1 b1" by blast
    from \<open>p'' \<in> q2_pre\<close> \<open>\<not> byz p''\<close> q2_pre have "(s\<cdot>pre_prepared) p'' v2 b2" by blast
    \<comment> \<open>By inv3, since p'' pre-prepared both b1 and b2 at the same view, they must be equal\<close>
    with \<open>(s\<cdot>pre_prepared) p'' v1 b1\<close> v1_eq_v2 \<open>\<not> byz p''\<close> \<open>inv3 s\<close>
    have "b1 = b2" unfolding inv3_def by blast
    thus ?thesis unfolding compatible_def by simp
  next
    case v2_lt_v1
    \<comment> \<open>v2 < v1: Show b2 \<le> b1 (symmetric to first case)\<close>
    from \<open>(s\<cdot>committed) p1 v1 b1\<close> \<open>\<not> byz p1\<close> \<open>inv1 s\<close> obtain q_prep where
      q_prep: "\<forall>p. p \<in> q_prep \<and> \<not> byz p \<longrightarrow> (s\<cdot>prepared) p v1 b1"
      unfolding inv1_def by blast
    obtain p_prep where "p_prep \<in> q_prep" "\<not> byz p_prep" "(s\<cdot>prepared) p_prep v1 b1"
      using q_prep by (metis quorum_intersection)
    from \<open>\<not> byz p_prep\<close> \<open>(s\<cdot>prepared) p_prep v1 b1\<close> \<open>inv2 s\<close> obtain q_pre where
      q_pre: "\<forall>p. p \<in> q_pre \<and> \<not> byz p \<longrightarrow> (s\<cdot>pre_prepared) p v1 b1"
      unfolding inv2_def by blast
    obtain p_pre where "p_pre \<in> q_pre" "\<not> byz p_pre" "(s\<cdot>pre_prepared) p_pre v1 b1"
      using q_pre by (metis quorum_intersection)
    from \<open>\<not> byz p_pre\<close> \<open>(s\<cdot>pre_prepared) p_pre v1 b1\<close> \<open>inv4 s\<close> have "safe s b1 v1"
      unfolding inv4_def by blast
    \<comment> \<open>Use safe_not_contradicted to get b2 \<le> b1\<close>
    from safe_not_contradicted[OF this v2_lt_v1 \<open>(s\<cdot>committed) p2 v2 b2\<close> \<open>\<not> byz p2\<close> \<open>inv1 s\<close> \<open>inv2 s\<close> \<open>inv3 s\<close> \<open>inv4 s\<close>]
    have "b2 \<le> b1" .
    thus ?thesis unfolding compatible_def by simp
  qed
qed

end