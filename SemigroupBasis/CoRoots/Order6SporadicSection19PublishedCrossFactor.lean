import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedPresentation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor

/-- Empty contexts are distinct from nonempty substitutions. -/
def gap (w : Word Nat) : Option (Word Nat) → Word Nat
  | none => w
  | some middle => w ++ middle

theorem c (u v : Word Nat) (hGap kGap tGap : Option (Word Nat)) :
    Derives basis ((gap ((gap ((gap u hGap) ++ v) kGap) ++ u) tGap) ++ v) ((((gap ((gap ((gap u hGap) ++ u) kGap) ++ u) tGap) ++ v) ++ v) ++ u) := by
  cases hGap with
  | none =>
      cases kGap with
      | none =>
          cases tGap with
          | none =>
              have step : Derives basis (c_000.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0))
                  (c_000.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)) := derives_c_000.subst (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)
              exact step
          | some t =>
              have step : Derives basis (c_100.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 4 => t | _ => Word.singleton 0))
                  (c_100.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 4 => t | _ => Word.singleton 0)) := derives_c_100.subst (fun n : Nat => match n with | 0 => u | 1 => v | 4 => t | _ => Word.singleton 0)
              exact step
      | some k =>
          cases tGap with
          | none =>
              have step : Derives basis (c_010.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0))
                  (c_010.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)) := derives_c_010.subst (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)
              exact step
          | some t =>
              have step : Derives basis (c_110.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | 4 => t | _ => Word.singleton 0))
                  (c_110.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | 4 => t | _ => Word.singleton 0)) := derives_c_110.subst (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | 4 => t | _ => Word.singleton 0)
              exact step
  | some h =>
      cases kGap with
      | none =>
          cases tGap with
          | none =>
              have step : Derives basis (c_001.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0))
                  (c_001.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)) := derives_c_001.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)
              exact step
          | some t =>
              have step : Derives basis (c_101.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 4 => t | _ => Word.singleton 0))
                  (c_101.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 4 => t | _ => Word.singleton 0)) := derives_c_101.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 4 => t | _ => Word.singleton 0)
              exact step
      | some k =>
          cases tGap with
          | none =>
              have step : Derives basis (c_011.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0))
                  (c_011.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)) := derives_c_011.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)
              exact step
          | some t =>
              have step : Derives basis (c_111.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | 4 => t | _ => Word.singleton 0))
                  (c_111.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | 4 => t | _ => Word.singleton 0)) := derives_c_111.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | 4 => t | _ => Word.singleton 0)
              exact step

theorem d_left (u v : Word Nat) (hGap : Option (Word Nat)) :
    Derives basis ((((gap u hGap) ++ v) ++ v) ++ u) ((((gap ((v ++ v) ++ u) hGap) ++ v) ++ v) ++ u) := by
  cases hGap with
  | none =>
      have step : Derives basis (d_left_0.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0))
          (d_left_0.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)) := derives_d_left_0.subst (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)
      exact step
  | some h =>
      have step : Derives basis (d_left_1.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0))
          (d_left_1.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)) := derives_d_left_1.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)
      exact step

theorem d_right (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis ((gap ((((gap u hGap) ++ v) ++ v) ++ u) kGap) ++ u) ((((gap ((((gap u hGap) ++ v) ++ v) ++ u) kGap) ++ v) ++ v) ++ u) := by
  cases hGap with
  | none =>
      cases kGap with
      | none =>
          have step : Derives basis (d_right_00.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0))
              (d_right_00.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)) := derives_d_right_00.subst (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (d_right_10.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0))
              (d_right_10.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)) := derives_d_right_10.subst (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)
          exact step
  | some h =>
      cases kGap with
      | none =>
          have step : Derives basis (d_right_01.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0))
              (d_right_01.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)) := derives_d_right_01.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (d_right_11.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0))
              (d_right_11.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)) := derives_d_right_11.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)
          exact step

theorem e_back (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis (((gap ((gap u hGap) ++ v) kGap) ++ u) ++ v) (((gap ((gap u hGap) ++ v) kGap) ++ v) ++ u) := by
  cases hGap with
  | none =>
      cases kGap with
      | none =>
          have step : Derives basis (e_back_00.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0))
              (e_back_00.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)) := derives_e_back_00.subst (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (e_back_10.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0))
              (e_back_10.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)) := derives_e_back_10.subst (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)
          exact step
  | some h =>
      cases kGap with
      | none =>
          have step : Derives basis (e_back_01.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0))
              (e_back_01.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)) := derives_e_back_01.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (e_back_11.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0))
              (e_back_11.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)) := derives_e_back_11.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)
          exact step

theorem e_front (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis (((gap ((gap u hGap) ++ v) kGap) ++ u) ++ v) (((gap ((gap v hGap) ++ u) kGap) ++ u) ++ v) := by
  cases hGap with
  | none =>
      cases kGap with
      | none =>
          have step : Derives basis (e_front_00.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0))
              (e_front_00.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)) := derives_e_front_00.subst (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (e_front_10.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0))
              (e_front_10.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)) := derives_e_front_10.subst (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)
          exact step
  | some h =>
      cases kGap with
      | none =>
          have step : Derives basis (e_front_01.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0))
              (e_front_01.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)) := derives_e_front_01.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (e_front_11.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0))
              (e_front_11.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)) := derives_e_front_11.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)
          exact step

theorem f_right (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis ((gap ((((gap u hGap) ++ v) ++ v) ++ u) kGap) ++ v) ((gap ((((gap u hGap) ++ v) ++ v) ++ u) kGap) ++ u) := by
  cases hGap with
  | none =>
      cases kGap with
      | none =>
          have step : Derives basis (f_right_00.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0))
              (f_right_00.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)) := derives_f_right_00.subst (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (f_right_10.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0))
              (f_right_10.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)) := derives_f_right_10.subst (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)
          exact step
  | some h =>
      cases kGap with
      | none =>
          have step : Derives basis (f_right_01.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0))
              (f_right_01.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)) := derives_f_right_01.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (f_right_11.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0))
              (f_right_11.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)) := derives_f_right_11.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)
          exact step

theorem f_left (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis ((((gap ((gap v hGap) ++ u) kGap) ++ v) ++ v) ++ u) ((((gap ((gap u hGap) ++ u) kGap) ++ v) ++ v) ++ u) := by
  cases hGap with
  | none =>
      cases kGap with
      | none =>
          have step : Derives basis (f_left_00.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0))
              (f_left_00.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)) := derives_f_left_00.subst (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (f_left_10.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0))
              (f_left_10.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)) := derives_f_left_10.subst (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)
          exact step
  | some h =>
      cases kGap with
      | none =>
          have step : Derives basis (f_left_01.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0))
              (f_left_01.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)) := derives_f_left_01.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (f_left_11.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0))
              (f_left_11.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)) := derives_f_left_11.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)
          exact step

theorem f_middle (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis ((((gap ((gap u hGap) ++ v) kGap) ++ v) ++ v) ++ u) ((((gap ((gap u hGap) ++ u) kGap) ++ v) ++ v) ++ u) := by
  cases hGap with
  | none =>
      cases kGap with
      | none =>
          have step : Derives basis (f_middle_00.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0))
              (f_middle_00.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)) := derives_f_middle_00.subst (fun n : Nat => match n with | 0 => u | 1 => v | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (f_middle_10.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0))
              (f_middle_10.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)) := derives_f_middle_10.subst (fun n : Nat => match n with | 0 => u | 1 => v | 3 => k | _ => Word.singleton 0)
          exact step
  | some h =>
      cases kGap with
      | none =>
          have step : Derives basis (f_middle_01.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0))
              (f_middle_01.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)) := derives_f_middle_01.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | _ => Word.singleton 0)
          exact step
      | some k =>
          have step : Derives basis (f_middle_11.lhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0))
              (f_middle_11.rhs.bind (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)) := derives_f_middle_11.subst (fun n : Nat => match n with | 0 => u | 1 => v | 2 => h | 3 => k | _ => Word.singleton 0)
          exact step

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor.c
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor.d_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor.d_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor.e_back
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor.e_front
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor.f_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor.f_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CrossFactor.f_middle
