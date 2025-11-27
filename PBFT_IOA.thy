theory PBFT_IOA
  imports "IOAutomata.IOA" "IOAutomata.Simulations" "IOAutomata.IOA_Automation" "HOL-Eisbach.Eisbach"
begin

section ‹Signature-Free PBFT as an I/O Automaton›

text ‹
  This theory reformulates the PBFT specification using the I/O Automata framework.
  The main benefit is enabling future refinement proofs using simulation relations
  between this abstract specification and more concrete message-passing implementations.
›

subsection ‹Preliminary Definitions›

definition compatible :: "'b::order ⇒ 'b ⇒ bool" where
  "compatible b b' ≡ b ≤ b' ∨ b' ≤ b"

subsection ‹State Type›

record ('p, 'v, 'b) pbft_state =
  committed :: "'p ⇒ 'v ⇒ 'b ⇒ bool"
  prepared :: "'p ⇒ 'v ⇒ 'b ⇒ bool"
  pre_prepared :: "'p ⇒ 'v ⇒ 'b ⇒ bool"
  cur_view :: "'p ⇒ 'v"

subsection ‹Action Type›

datatype ('p, 'q, 'v, 'b) pbft_action =
    ActCommit 'p 'q 'v 'b      ― ‹party p commits block b in view v with quorum q witness›
  | ActPrepare 'p 'q 'v 'b     ― ‹party p prepares block b in view v with quorum q witness›
  | ActPrePrepare 'p 'v 'b     ― ‹party p pre-prepares block b in view v›
  | ActChangeView 'p 'v        ― ‹party p changes to view v›
  | ActByzantineHavoc          ― ‹internal action for byzantine behavior›

subsection ‹PBFT Locale›

locale pbft_ioa =
  fixes quorum_member :: "'p ⇒ 'q ⇒ bool"
    and byz :: "'p ⇒ bool"
  assumes quorum_intersection: "⋀q1 q2. ∃p. ¬ byz p ∧ quorum_member p q1 ∧ quorum_member p q2"
begin

subsection ‹Safe Predicate›

text ‹
  A block b is safe at view v if there exists a witness view v' < v and a quorum q such that:
  - All honest parties in q have view ≥ v
  - No honest party in q has prepared anything in views between v' and v
  - No honest party in q has pre-prepared a different block at v'
  - Some honest party has pre-prepared b at v'
›

definition safe :: "('p, 'v::wellorder, 'b) pbft_state ⇒ 'b ⇒ 'v ⇒ bool" where
  "safe s b v ≡ ∃v'. v' < v
    ∧ (∃q. ∀p. quorum_member p q ∧ ¬ byz p ⟶
          cur_view s p ≥ v
        ∧ (∀v'' b''. v' < v'' ∧ v'' < v ⟶ ¬ prepared s p v'' b'')
        ∧ (∀b'. b' ≠ b ⟶ ¬ pre_prepared s p v' b'))
    ∧ (∃p. ¬ byz p ∧ pre_prepared s p v' b)"

subsection ‹Signature›

definition pbft_sig :: "(('p, 'q, 'v::wellorder, 'b) pbft_action) signature" where
  "pbft_sig ≡ ⦇
    inputs = {},
    outputs = {a. ∃p q v b. a = ActCommit p q v b},
    internals = {a. (∃p q v b. a = ActPrepare p q v b) 
               ∨ (∃p v b. a = ActPrePrepare p v b)
               ∨ (∃p v. a = ActChangeView p v)
               ∨ a = ActByzantineHavoc}
  ⦈"

subsection ‹Initial States›

definition pbft_start :: "('p, 'v::wellorder, 'b) pbft_state set" where
  "pbft_start ≡ {s. ∀p v b. 
      ¬ committed s p v b 
    ∧ ¬ prepared s p v b 
    ∧ ¬ pre_prepared s p v b}"

subsection ‹Transition Relation›

text ‹Individual transition predicates›

definition trans_commit :: "('p, 'v::wellorder, 'b) pbft_state ⇒ 'p ⇒ 'q ⇒ 'v ⇒ 'b ⇒ ('p, 'v, 'b) pbft_state ⇒ bool" where
  "trans_commit s p q v b s' ≡
      ¬ byz p
    ∧ v = cur_view s p
    ∧ (∀p'. quorum_member p' q ∧ ¬ byz p' ⟶ prepared s p' v b)
    ∧ s' = s⦇committed := (committed s)(p := (committed s p)(v := (committed s p v)(b := True)))⦈"

definition trans_prepare :: "('p, 'v::wellorder, 'b) pbft_state ⇒ 'p ⇒ 'q ⇒ 'v ⇒ 'b ⇒ ('p, 'v, 'b) pbft_state ⇒ bool" where
  "trans_prepare s p q v b s' ≡
      ¬ byz p
    ∧ v = cur_view s p
    ∧ (∀p'. quorum_member p' q ∧ ¬ byz p' ⟶ pre_prepared s p' v b)
    ∧ s' = s⦇prepared := (prepared s)(p := (prepared s p)(v := (prepared s p v)(b := True)))⦈"

definition trans_pre_prepare :: "('p, 'v::wellorder, 'b) pbft_state ⇒ 'p ⇒ 'v ⇒ 'b ⇒ ('p, 'v, 'b) pbft_state ⇒ bool" where
  "trans_pre_prepare s p v b s' ≡
      ¬ byz p
    ∧ v = cur_view s p
    ∧ safe s b v
    ∧ (∀b'. ¬ pre_prepared s p v b')
    ∧ s' = s⦇pre_prepared := (pre_prepared s)(p := (pre_prepared s p)(v := (pre_prepared s p v)(b := True)))⦈"

definition trans_change_view :: "('p, 'v::wellorder, 'b) pbft_state ⇒ 'p ⇒ 'v ⇒ ('p, 'v, 'b) pbft_state ⇒ bool" where
  "trans_change_view s p v s' ≡
      ¬ byz p
    ∧ cur_view s p < v
    ∧ s' = s⦇cur_view := (cur_view s)(p := v)⦈"

definition trans_byzantine_havoc :: "('p, 'v::wellorder, 'b) pbft_state ⇒ ('p, 'v, 'b) pbft_state ⇒ bool" where
  "trans_byzantine_havoc s s' ≡
    ∀p' v b. ¬ byz p' ⟶ 
        committed s' p' v b = committed s p' v b ∧
        prepared s' p' v b = prepared s p' v b ∧
        pre_prepared s' p' v b = pre_prepared s p' v b ∧
        cur_view s' p' = cur_view s p'"

text ‹Combined transition set›

definition pbft_trans :: 
  "(('p, 'v::wellorder, 'b) pbft_state, ('p, 'q, 'v, 'b) pbft_action) transition set" where
  "pbft_trans ≡ 
     {(s, ActCommit p q v b, s') | s s' p q v b. trans_commit s p q v b s'}
   ∪ {(s, ActPrepare p q v b, s') | s s' p q v b. trans_prepare s p q v b s'}
   ∪ {(s, ActPrePrepare p v b, s') | s s' p v b. trans_pre_prepare s p v b s'}
   ∪ {(s, ActChangeView p v, s') | s s' p v. trans_change_view s p v s'}
   ∪ {(s, ActByzantineHavoc, s') | s s'. trans_byzantine_havoc s s'}"

subsection ‹The PBFT I/O Automaton›

definition pbft :: "(('p, 'v::wellorder, 'b) pbft_state, ('p, 'q, 'v, 'b) pbft_action) ioa" where
  "pbft ≡ ioa.make pbft_sig pbft_start pbft_trans"

subsection ‹Transition Lemmas›

lemma pbft_transI_commit:
  "trans_commit s p q v b s' ⟹ (s, ActCommit p q v b, s') ∈ pbft_trans"
  unfolding pbft_trans_def by auto

lemma pbft_transI_prepare:
  "trans_prepare s p q v b s' ⟹ (s, ActPrepare p q v b, s') ∈ pbft_trans"
  unfolding pbft_trans_def by auto

lemma pbft_transI_pre_prepare:
  "trans_pre_prepare s p v b s' ⟹ (s, ActPrePrepare p v b, s') ∈ pbft_trans"
  unfolding pbft_trans_def by auto

lemma pbft_transI_change_view:
  "trans_change_view s p v s' ⟹ (s, ActChangeView p v, s') ∈ pbft_trans"
  unfolding pbft_trans_def by auto

lemma pbft_transI_byzantine_havoc:
  "trans_byzantine_havoc s s' ⟹ (s, ActByzantineHavoc, s') ∈ pbft_trans"
  unfolding pbft_trans_def by auto

lemma pbft_trans_cases[consumes 1, case_names commit prepare pre_prepare change_view byzantine_havoc]:
  assumes "(s, a, s') ∈ pbft_trans"
  obtains (commit) p q v b where "a = ActCommit p q v b" "trans_commit s p q v b s'"
    | (prepare) p q v b where "a = ActPrepare p q v b" "trans_prepare s p q v b s'"
    | (pre_prepare) p v b where "a = ActPrePrepare p v b" "trans_pre_prepare s p v b s'"
    | (change_view) p v where "a = ActChangeView p v" "trans_change_view s p v s'"
    | (byzantine_havoc) "a = ActByzantineHavoc" "trans_byzantine_havoc s s'"
  using assms unfolding pbft_trans_def by auto

subsection ‹Invariant Definitions›

definition inv0 :: "('p, 'v::wellorder, 'b) pbft_state ⇒ bool" where
  "inv0 s ≡ ∀p v b. ¬ byz p ⟶ 
    (pre_prepared s p v b ∨ prepared s p v b ∨ committed s p v b) ⟶ 
    v ≤ cur_view s p"

definition inv1 :: "('p, 'v::wellorder, 'b) pbft_state ⇒ bool" where
  "inv1 s ≡ ∀p v b. ¬ byz p ∧ committed s p v b ⟶ 
    (∃q. ∀p'. quorum_member p' q ∧ ¬ byz p' ⟶ prepared s p' v b)"

definition inv2 :: "('p, 'v::wellorder, 'b) pbft_state ⇒ bool" where
  "inv2 s ≡ ∀p v b. ¬ byz p ∧ prepared s p v b ⟶ 
    (∃q. ∀p'. quorum_member p' q ∧ ¬ byz p' ⟶ pre_prepared s p' v b)"

definition inv3 :: "('p, 'v::wellorder, 'b) pbft_state ⇒ bool" where
  "inv3 s ≡ ∀p v b b'. ¬ byz p ∧ pre_prepared s p v b ∧ pre_prepared s p v b' ⟶ b = b'"

definition inv4 :: "('p, 'v::wellorder, 'b) pbft_state ⇒ bool" where
  "inv4 s ≡ ∀p v b. ¬ byz p ∧ pre_prepared s p v b ⟶ safe s b v"

subsection ‹VCG Methods for IOA›

text ‹Named theorem collections for automation›

named_theorems ioa_trans_defs
declare trans_commit_def[ioa_trans_defs]
declare trans_prepare_def[ioa_trans_defs]
declare trans_pre_prepare_def[ioa_trans_defs]
declare trans_change_view_def[ioa_trans_defs]
declare trans_byzantine_havoc_def[ioa_trans_defs]

text ‹Register definitions for IOA_Automation (within IOA context)›
declare trans_commit_def[IOA.inv_proofs_defs]
declare trans_prepare_def[IOA.inv_proofs_defs]
declare trans_pre_prepare_def[IOA.inv_proofs_defs]
declare trans_change_view_def[IOA.inv_proofs_defs]
declare trans_byzantine_havoc_def[IOA.inv_proofs_defs]
declare pbft_trans_def[IOA.inv_proofs_defs]
declare pbft_start_def[IOA.inv_proofs_defs]
declare pbft_def[IOA.inv_proofs_defs]
declare ioa.make_def[IOA.inv_proofs_defs]
declare inv0_def[IOA.inv_proofs_defs]

text ‹VCG method using IOA transition cases›
method ioa_inv_vcg uses inv_def =
  (unfold ioa_trans_defs inv_def,
   auto split: if_splits,
   ((force | fastforce | meson | blast)+)?)

text ‹Prove initial state satisfies invariant›
method ioa_prove_init uses inv_def =
  (simp add: pbft_start_def inv_def pbft_def ioa.make_def)

subsection ‹Invariant Proofs›

theorem inv0_invariant: "IOA.invariant pbft inv0"
  apply (IOA.prove_invariant)
     apply (force|fastforce|metis|meson|blast)+
  done

theorem inv1_invariant: "IOA.invariant pbft inv1"
  apply (IOA.prove_invariant inv_proofs_defs: inv1_def)
     apply (force|fastforce|metis|meson|blast)+
  done

theorem inv2_invariant: "IOA.invariant pbft inv2"
  apply (IOA.prove_invariant inv_proofs_defs: inv2_def)
    apply IOA.auto_finish
  done

theorem inv3_invariant: "IOA.invariant pbft inv3"
  apply (IOA.prove_invariant inv_proofs_defs: inv3_def)
    apply IOA.auto_finish
  done

subsection ‹Safe Preservation Lemma›

lemma safe_preserved:
  assumes "safe s b v" and "(s, a, s') ∈ pbft_trans"
  shows "safe s' b v"
proof -
  from ‹safe s b v› obtain v_wit q_wit pa where
    v_wit_lt: "v_wit < v" and
    q_wit: "∀pa. quorum_member pa q_wit ∧ ¬ byz pa ⟶
          cur_view s pa ≥ v
        ∧ (∀v'' b''. v_wit < v'' ∧ v'' < v ⟶ ¬ prepared s pa v'' b'')
        ∧ (∀bc. bc ≠ b ⟶ ¬ pre_prepared s pa v_wit bc)" and
    witness_exists: "¬ byz pa ∧ pre_prepared s pa v_wit b"
    unfolding safe_def by auto
  
  from assms(2) show ?thesis
  proof (cases rule: pbft_trans_cases)
    case (commit p q v' b')
    hence q_wit': "∀pa. quorum_member pa q_wit ∧ ¬ byz pa ⟶
          cur_view s' pa ≥ v
        ∧ (∀v'' b''. v_wit < v'' ∧ v'' < v ⟶ ¬ prepared s' pa v'' b'')
        ∧ (∀bc. bc ≠ b ⟶ ¬ pre_prepared s' pa v_wit bc)"
      and witness_exists': "¬ byz pa ∧ pre_prepared s' pa v_wit b"
      using q_wit witness_exists unfolding trans_commit_def by auto
    thus ?thesis using v_wit_lt unfolding safe_def by blast
  next
    case (prepare p q v' b')
    hence q_wit': "∀pa. quorum_member pa q_wit ∧ ¬ byz pa ⟶
          cur_view s' pa ≥ v
        ∧ (∀v'' b''. v_wit < v'' ∧ v'' < v ⟶ ¬ prepared s' pa v'' b'')
        ∧ (∀bc. bc ≠ b ⟶ ¬ pre_prepared s' pa v_wit bc)"
      and witness_exists': "¬ byz pa ∧ pre_prepared s' pa v_wit b"
      using q_wit witness_exists unfolding trans_prepare_def by auto
    thus ?thesis using v_wit_lt unfolding safe_def by blast
  next
    case (pre_prepare p v' b')
    hence q_wit': "∀pa. quorum_member pa q_wit ∧ ¬ byz pa ⟶
          cur_view s' pa ≥ v
        ∧ (∀v'' b''. v_wit < v'' ∧ v'' < v ⟶ ¬ prepared s' pa v'' b'')
        ∧ (∀bc. bc ≠ b ⟶ ¬ pre_prepared s' pa v_wit bc)"
      and witness_exists': "¬ byz pa ∧ pre_prepared s' pa v_wit b"
      using q_wit witness_exists unfolding trans_pre_prepare_def apply auto
      by (metis linorder_not_less v_wit_lt) 
    thus ?thesis using v_wit_lt unfolding safe_def by blast
  next
    case (change_view p v')
    hence q_wit': "∀pa. quorum_member pa q_wit ∧ ¬ byz pa ⟶
          cur_view s' pa ≥ v
        ∧ (∀v'' b''. v_wit < v'' ∧ v'' < v ⟶ ¬ prepared s' pa v'' b'')
        ∧ (∀bc. bc ≠ b ⟶ ¬ pre_prepared s' pa v_wit bc)"
      and witness_exists': "¬ byz pa ∧ pre_prepared s' pa v_wit b"
      using q_wit witness_exists unfolding trans_change_view_def by auto
    thus ?thesis using v_wit_lt unfolding safe_def by blast
  next
    case byzantine_havoc
    hence q_wit': "∀pa. quorum_member pa q_wit ∧ ¬ byz pa ⟶
          cur_view s' pa ≥ v
        ∧ (∀v'' b''. v_wit < v'' ∧ v'' < v ⟶ ¬ prepared s' pa v'' b'')
        ∧ (∀bc. bc ≠ b ⟶ ¬ pre_prepared s' pa v_wit bc)"
      and witness_exists': "¬ byz pa ∧ pre_prepared s' pa v_wit b"
      using q_wit witness_exists unfolding trans_byzantine_havoc_def by auto
    thus ?thesis using v_wit_lt unfolding safe_def by blast
  qed
qed

theorem inv4_invariant: "IOA.invariant pbft inv4"
proof (rule IOA.invariantI)
  fix s assume "s ∈ start pbft"
  thus "inv4 s" 
    by (simp add: pbft_start_def inv4_def safe_def pbft_def)
next
  fix s t a
  assume reach: "IOA.reachable pbft s" and inv: "inv4 s" 
    and step: "s ─a─pbft⟶ t"
  from step have trans: "(s, a, t) ∈ pbft_trans"
    unfolding IOA.is_trans_def pbft_def by simp
  show "inv4 t"
  proof (cases rule: pbft_trans_cases[OF trans])
    case (commit p q v b)
    show ?thesis unfolding inv4_def
    proof (intro allI impI)
      fix pa va ba
      assume "¬ byz pa ∧ pre_prepared t pa va ba"
      then have "¬ byz pa" and "pre_prepared s pa va ba"
        using commit unfolding trans_commit_def by auto
      from inv ‹¬ byz pa› ‹pre_prepared s pa va ba› have "safe s ba va"
        unfolding inv4_def by blast
      thus "safe t ba va" using safe_preserved trans by blast
    qed
  next
    case (prepare p q v b)
    show ?thesis unfolding inv4_def
    proof (intro allI impI)
      fix pa va ba
      assume "¬ byz pa ∧ pre_prepared t pa va ba"
      then have "¬ byz pa" and "pre_prepared s pa va ba"
        using prepare unfolding trans_prepare_def by auto
      from inv ‹¬ byz pa› ‹pre_prepared s pa va ba› have "safe s ba va"
        unfolding inv4_def by blast
      thus "safe t ba va" using safe_preserved trans by blast
    qed
  next
    case (pre_prepare p v b)
    show ?thesis unfolding inv4_def
    proof (intro allI impI)
      fix pa va ba
      assume asm: "¬ byz pa ∧ pre_prepared t pa va ba"
      then have pa_correct: "¬ byz pa" by blast
      show "safe t ba va"
      proof (cases "pa = p ∧ va = v ∧ ba = b")
        case True
        from pre_prepare have "safe s b v" unfolding trans_pre_prepare_def by blast
        with True show ?thesis using safe_preserved trans by blast
      next
        case False
        from False asm pre_prepare have "pre_prepared s pa va ba"
          unfolding trans_pre_prepare_def by (auto split: if_splits)
        from inv pa_correct this have "safe s ba va"
          unfolding inv4_def by blast
        thus ?thesis using safe_preserved trans by blast
      qed
    qed
  next
    case (change_view p v)
    show ?thesis unfolding inv4_def
    proof (intro allI impI)
      fix pa va ba
      assume "¬ byz pa ∧ pre_prepared t pa va ba"
      then have "¬ byz pa" and "pre_prepared s pa va ba"
        using change_view unfolding trans_change_view_def by auto
      from inv ‹¬ byz pa› ‹pre_prepared s pa va ba› have "safe s ba va"
        unfolding inv4_def by blast
      thus "safe t ba va" using safe_preserved trans by blast
    qed
  next
    case byzantine_havoc
    show ?thesis unfolding inv4_def
    proof (intro allI impI)
      fix pa va ba
      assume "¬ byz pa ∧ pre_prepared t pa va ba"
      then have "¬ byz pa" and "pre_prepared s pa va ba"
        using byzantine_havoc unfolding trans_byzantine_havoc_def by auto
      from inv ‹¬ byz pa› ‹pre_prepared s pa va ba› have "safe s ba va"
        unfolding inv4_def by blast
      thus "safe t ba va" using safe_preserved trans by blast
    qed
  qed
qed

subsection ‹Auxiliary Lemmas for Safety Theorem›

lemma prepare_blocks_equal:
  assumes "¬ byz p'" "prepared s p' v b'" 
    and "∀p''. quorum_member p'' q ∧ ¬ byz p'' ⟶ pre_prepared s p'' v b"
    and "inv2 s" "inv3 s"
  shows "b = b'"
proof -
  from assms(1,2,4) obtain q' where
    "∀p''. quorum_member p'' q' ∧ ¬ byz p'' ⟶ pre_prepared s p'' v b'"
    unfolding inv2_def by blast
  obtain p'' where "¬ byz p''" "quorum_member p'' q" "quorum_member p'' q'"
    using quorum_intersection by blast
  with assms(3) have "pre_prepared s p'' v b" by blast
  from ‹∀p''. quorum_member p'' q' ∧ ¬ byz p'' ⟶ pre_prepared s p'' v b'› ‹¬ byz p''› ‹quorum_member p'' q'›
  have "pre_prepared s p'' v b'" by blast
  from assms(5) ‹¬ byz p''› ‹pre_prepared s p'' v b› ‹pre_prepared s p'' v b'›
  show "b = b'" unfolding inv3_def by blast
qed

lemma safe_not_contradicted:
  assumes "safe s b v" and "v' < v" and "committed s p v' b'"
    and "¬ byz p"
    and "inv1 s" and "inv2 s" and "inv3 s" and "inv4 s"
  shows "b' ≤ b"
using assms
proof (induction v arbitrary: b p rule: less_induct)
  case (less v)
  from ‹safe s b v› obtain v_wit q where
    v_wit_less: "v_wit < v" and
    q_safe: "∀pa. quorum_member pa q ∧ ¬ byz pa ⟶ 
        cur_view s pa ≥ v 
      ∧ (∀v'' b''. v_wit < v'' ∧ v'' < v ⟶ ¬ prepared s pa v'' b'')
      ∧ (∀b'. b' ≠ b ⟶ ¬ pre_prepared s pa v_wit b')" and
    witness_b: "∃pa. ¬ byz pa ∧ pre_prepared s pa v_wit b"
    unfolding safe_def by auto
  
  from ‹¬ byz p› ‹committed s p v' b'› ‹inv1 s›
  obtain q_prep where q_prep: "∀pa. quorum_member pa q_prep ∧ ¬ byz pa ⟶ prepared s pa v' b'"
    unfolding inv1_def by blast
  
  consider (before) "v' < v_wit" | (at) "v' = v_wit" | (between) "v_wit < v' ∧ v' < v"
    using ‹v' < v› v_wit_less by force
  then show ?case
  proof cases
    case before
    from witness_b obtain p_wit where
      p_wit_props: "¬ byz p_wit" "pre_prepared s p_wit v_wit b"
      by blast
    from p_wit_props ‹inv4 s› have "safe s b v_wit"
      unfolding inv4_def by blast
    from less.IH[OF v_wit_less this before ‹committed s p v' b'› ‹¬ byz p› ‹inv1 s› ‹inv2 s› ‹inv3 s› ‹inv4 s›]
    show ?thesis .
  next
    case at
    obtain p_prep where p_prep_props: "quorum_member p_prep q_prep" "¬ byz p_prep" "prepared s p_prep v' b'"
      using q_prep by (metis quorum_intersection)
    from p_prep_props(2,3) ‹inv2 s› obtain q_pre where
      q_pre: "∀pa. quorum_member pa q_pre ∧ ¬ byz pa ⟶ pre_prepared s pa v' b'"
      unfolding inv2_def by blast
    obtain p'' where p''_props: "¬ byz p''" "quorum_member p'' q" "quorum_member p'' q_pre"
      using quorum_intersection by blast
    from p''_props(1,3) q_pre have "pre_prepared s p'' v' b'" by blast
    with at have "pre_prepared s p'' v_wit b'" by simp
    from p''_props(1,2) q_safe have "∀b'. b' ≠ b ⟶ ¬ pre_prepared s p'' v_wit b'" by blast
    with ‹pre_prepared s p'' v_wit b'› have "b' = b" by blast
    thus ?thesis by simp
  next
    case between 
    obtain p'' where "¬ byz p''" "quorum_member p'' q" "quorum_member p'' q_prep"
      using quorum_intersection by blast
    with q_safe between have "¬ prepared s p'' v' b'" by blast
    moreover from ‹quorum_member p'' q_prep› ‹¬ byz p''› q_prep have "prepared s p'' v' b'"
      by blast
    ultimately show ?thesis by blast
  qed
qed

subsection ‹Main Safety Theorem›

theorem committed_blocks_compatible:
  assumes "committed s p1 v1 b1" "¬ byz p1"
      and "committed s p2 v2 b2" "¬ byz p2"
      and "inv1 s" "inv2 s" "inv3 s" "inv4 s"
  shows "compatible b1 b2"
proof -
  consider (v1_lt_v2) "v1 < v2" | (v1_eq_v2) "v1 = v2" | (v2_lt_v1) "v2 < v1"
    by force
  then show ?thesis
  proof cases
    case v1_lt_v2
    from ‹committed s p2 v2 b2› ‹¬ byz p2› ‹inv1 s› obtain q_prep where
      q_prep: "∀p. quorum_member p q_prep ∧ ¬ byz p ⟶ prepared s p v2 b2"
      unfolding inv1_def by blast
    obtain p_prep where "quorum_member p_prep q_prep" "¬ byz p_prep" "prepared s p_prep v2 b2"
      using q_prep by (metis quorum_intersection)
    from ‹¬ byz p_prep› ‹prepared s p_prep v2 b2› ‹inv2 s› obtain q_pre where
      q_pre: "∀p. quorum_member p q_pre ∧ ¬ byz p ⟶ pre_prepared s p v2 b2"
      unfolding inv2_def by blast
    obtain p_pre where "quorum_member p_pre q_pre" "¬ byz p_pre" "pre_prepared s p_pre v2 b2"
      using q_pre by (metis quorum_intersection)
    from ‹¬ byz p_pre› ‹pre_prepared s p_pre v2 b2› ‹inv4 s› have "safe s b2 v2"
      unfolding inv4_def by blast
    from safe_not_contradicted[OF this v1_lt_v2 ‹committed s p1 v1 b1› ‹¬ byz p1› ‹inv1 s› ‹inv2 s› ‹inv3 s› ‹inv4 s›]
    have "b1 ≤ b2" .
    thus ?thesis unfolding compatible_def by simp
  next
    case v1_eq_v2
    from ‹committed s p1 v1 b1› ‹¬ byz p1› ‹inv1 s› obtain q1_prep where
      q1_prep: "∀p. quorum_member p q1_prep ∧ ¬ byz p ⟶ prepared s p v1 b1"
      unfolding inv1_def by blast
    from ‹committed s p2 v2 b2› ‹¬ byz p2› ‹inv1 s› obtain q2_prep where
      q2_prep: "∀p. quorum_member p q2_prep ∧ ¬ byz p ⟶ prepared s p v2 b2"
      unfolding inv1_def by blast
    obtain p1_prep where "quorum_member p1_prep q1_prep" "¬ byz p1_prep" "prepared s p1_prep v1 b1"
      using q1_prep by (metis quorum_intersection)
    from ‹¬ byz p1_prep› ‹prepared s p1_prep v1 b1› ‹inv2 s› obtain q1_pre where
      q1_pre: "∀p. quorum_member p q1_pre ∧ ¬ byz p ⟶ pre_prepared s p v1 b1"
      unfolding inv2_def by blast
    obtain p2_prep where "quorum_member p2_prep q2_prep" "¬ byz p2_prep" "prepared s p2_prep v2 b2"
      using q2_prep by (metis quorum_intersection)
    from ‹¬ byz p2_prep› ‹prepared s p2_prep v2 b2› ‹inv2 s› obtain q2_pre where
      q2_pre: "∀p. quorum_member p q2_pre ∧ ¬ byz p ⟶ pre_prepared s p v2 b2"
      unfolding inv2_def by blast
    obtain p'' where "¬ byz p''" "quorum_member p'' q1_pre" "quorum_member p'' q2_pre"
      using quorum_intersection by blast
    from ‹quorum_member p'' q1_pre› ‹¬ byz p''› q1_pre have "pre_prepared s p'' v1 b1" by blast
    from ‹quorum_member p'' q2_pre› ‹¬ byz p''› q2_pre have "pre_prepared s p'' v2 b2" by blast
    with ‹pre_prepared s p'' v1 b1› v1_eq_v2 ‹¬ byz p''› ‹inv3 s›
    have "b1 = b2" unfolding inv3_def by blast
    thus ?thesis unfolding compatible_def by simp
  next
    case v2_lt_v1
    from ‹committed s p1 v1 b1› ‹¬ byz p1› ‹inv1 s› obtain q_prep where
      q_prep: "∀p. quorum_member p q_prep ∧ ¬ byz p ⟶ prepared s p v1 b1"
      unfolding inv1_def by blast
    obtain p_prep where "quorum_member p_prep q_prep" "¬ byz p_prep" "prepared s p_prep v1 b1"
      using q_prep by (metis quorum_intersection)
    from ‹¬ byz p_prep› ‹prepared s p_prep v1 b1› ‹inv2 s› obtain q_pre where
      q_pre: "∀p. quorum_member p q_pre ∧ ¬ byz p ⟶ pre_prepared s p v1 b1"
      unfolding inv2_def by blast
    obtain p_pre where "quorum_member p_pre q_pre" "¬ byz p_pre" "pre_prepared s p_pre v1 b1"
      using q_pre by (metis quorum_intersection)
    from ‹¬ byz p_pre› ‹pre_prepared s p_pre v1 b1› ‹inv4 s› have "safe s b1 v1"
      unfolding inv4_def by blast
    from safe_not_contradicted[OF this v2_lt_v1 ‹committed s p2 v2 b2› ‹¬ byz p2› ‹inv1 s› ‹inv2 s› ‹inv3 s› ‹inv4 s›]
    have "b2 ≤ b1" .
    thus ?thesis unfolding compatible_def by simp
  qed
qed

text ‹Main safety property: all committed blocks in reachable states are compatible›

theorem safety:
  assumes "IOA.reachable pbft s"
    and "committed s p1 v1 b1" "¬ byz p1"
    and "committed s p2 v2 b2" "¬ byz p2"
  shows "compatible b1 b2"
proof -
  from inv0_invariant inv1_invariant inv2_invariant inv3_invariant inv4_invariant assms(1)
  have "inv0 s" "inv1 s" "inv2 s" "inv3 s" "inv4 s"
    unfolding IOA.invariant_def by auto
  thus ?thesis using committed_blocks_compatible assms(2-5) by blast
qed

end

end
