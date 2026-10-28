import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.SubschemeDescent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyLocality

/-! # Family Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyDescent

noncomputable section

/-! Compatible native Hilbert families on an open cover descend to an
actual global ideal-sheaf family with flat, proper, finitely presented projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S) {T : Over S} {J : Type u}
variable (U : J → Over S) (f : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (f i).left]
variable (hcover : ∀ t : T.left, ∃ i, ∃ y : (U i).left, (f i).left y = t)
variable (F : ∀ i, Functor.Family X (U i))
variable (hc : ∀ i j, Functor.pullbackFamily X (pullback.fst (f i) (f j)) (F i) =
  Functor.pullbackFamily X (pullback.snd (f i) (f j)) (F j))

include hc in
omit [∀ i, IsOpenImmersion (f i).left] in
theorem familyDescent_closed_compatibility (i j : J) :
    (F i).val.subschemeι.ker.comap (pullback.fst (Functor.ambientMap X (f i)) (Functor.ambientMap X (f j))) =
      (F j).val.subschemeι.ker.comap (pullback.snd (Functor.ambientMap X (f i)) (Functor.ambientMap X (f j))) := by
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  exact AmbientCover.ambient_overlap_ideal_compatibility X (f i) (f j) (F i).val (F j).val
    (congrArg Subtype.val (hc i j))

def descendedFamilyIdeal : (Functor.ambient X T).IdealSheafData := by
  let C := AmbientCover.ambientOpenCover X U f hcover
  let Z : C.I₀ → Scheme.{u} := fun i => (F i).val.subscheme
  let c : ∀ i, Z i ⟶ C.X i := fun i => (F i).val.subschemeι
  have hclosed : ∀ i, IsClosedImmersion (c i) := fun i =>
    inferInstanceAs (IsClosedImmersion (F i).val.subschemeι)
  exact @Closed.SubschemeDescent.descendedClosedIdeal (Functor.ambient X T) C Z c hclosed (familyDescent_closed_compatibility X U f F hc)

theorem descendedFamilyIdeal_comap (i : J) :
    (descendedFamilyIdeal X U f hcover F hc).comap (Functor.ambientMap X (f i)) = (F i).val := by
  let C := AmbientCover.ambientOpenCover X U f hcover
  let Z : C.I₀ → Scheme.{u} := fun i => (F i).val.subscheme
  let c : ∀ i, Z i ⟶ C.X i := fun i => (F i).val.subschemeι
  have hclosed : ∀ i, IsClosedImmersion (c i) := fun i =>
    inferInstanceAs (IsClosedImmersion (F i).val.subschemeι)
  have H := @Closed.SubschemeDescent.descendedClosedIdeal_comap (Functor.ambient X T) C Z c hclosed
    (familyDescent_closed_compatibility X U f F hc) i
  exact H.trans (Scheme.IdealSheafData.ker_subschemeι _)

def descendedFamily : Functor.Family X T :=
  ⟨descendedFamilyIdeal X U f hcover F hc, FamilyLocality.isFamily_of_openCover X U f hcover _ (fun i => by
    rw [descendedFamilyIdeal_comap]
    exact (F i).property)⟩

theorem descendedFamily_restriction (i : J) :
    Functor.pullbackFamily X (f i) (descendedFamily X U f hcover F hc) = F i := by
  apply Subtype.ext
  exact descendedFamilyIdeal_comap X U f hcover F hc i

include hcover hc in
theorem family_descent : ∃ G : Functor.Family X T, ∀ i, Functor.pullbackFamily X (f i) G = F i :=
  ⟨descendedFamily X U f hcover F hc, descendedFamily_restriction X U f hcover F hc⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyDescent
