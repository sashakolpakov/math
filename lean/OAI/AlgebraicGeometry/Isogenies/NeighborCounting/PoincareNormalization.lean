import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedIso

/-! # Poincare Normalization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

noncomputable section

/-! Normalized local comparison of the independently specified Poincare
bundles. Both zero-section trivializations come from the native dual data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareLocal OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedIso

variable {S : Scheme.{u}} {a b : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b S}

def familyZero (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S) (T : Over S) : T ⟶ T ⊗ A.scheme :=
  lift (𝟙 T) (1 : T ⟶ A.scheme)

theorem familyZero_projection (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S) (T : Over S) :
    (familyZero A T).left ≫ (fst T A.scheme).left = 𝟙 T.left := by
  exact congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A.scheme))

theorem familyZero_naturality (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S)
    {T U : Over S} (t : U ⟶ T) :
    familyZero A U ≫ (t ▷ A.scheme) = t ≫ familyZero A T := by
  apply hom_ext <;> simp [familyZero]

theorem familyZero_hom (f : A.scheme ⟶ B.scheme) [IsMonHom f] (T : Over S) :
    familyZero A T ≫ (T ◁ f) = familyZero B T := by
  apply hom_ext <;> simp [familyZero, MonObj.one_comp]

def IsNormalized (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S) (T : Over S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left) : Prop :=
  Nonempty ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (familyZero A T).left L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)

theorem normalized_iff_class (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S) (T : Over S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left) :
    IsNormalized A T L ↔ AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (familyZero A T).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass T.left := by
  constructor
  · intro h
    exact Quotient.sound h
  · intro h
    exact Quotient.exact h

theorem normalized_family_pullback (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S)
    {T U : Over S} (t : U ⟶ T) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (hL : IsNormalized A T L) :
    IsNormalized A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (t ▷ A.scheme).left L) := by
  apply (normalized_iff_class A U _).mpr
  have h := (normalized_iff_class A T L).mp hL
  have hz := congrArg Over.Hom.left (familyZero_naturality A t)
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (familyZero A U).left (t ▷ A.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
    ((congrArg (fun z ↦ AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hz).trans
      ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp t.left (familyZero A T).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).trans
        ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t.left) h).trans
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial t.left))))

/-- Pull back a fixed zero-section trivialization through the actual
cartesian square; this retains the same choice on all cover members. -/
def familyPullbackZeroIso (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S) {T U : Over S} (t : U ⟶ T)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (eL : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (familyZero A T).left L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (familyZero A U).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (t ▷ A.scheme).left L)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left :=
  (Scheme.Modules.pullbackComp (familyZero A U).left (t ▷ A.scheme).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      (familyZero_naturality A t))).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp t.left (familyZero A T).left).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback t.left).mapIso eL ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t.left

variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

theorem abelianPull_normalized (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    IsNormalized A DB.abelian.scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DB.abelian.scheme ◁ f).left DB.poincare) := by
  apply (normalized_iff_class A DB.abelian.scheme _).mpr
  have hz := congrArg Over.Hom.left (familyZero_hom f DB.abelian.scheme)
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (familyZero A DB.abelian.scheme).left
    (DB.abelian.scheme ◁ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)).symm.trans
    ((congrArg (fun z ↦ AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) hz).trans
      (Quotient.sound DB.normalizedAtAbelianZero))

theorem dualPull_normalized (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    IsNormalized A DB.abelian.scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DualComparison.dualMap DA DB f ▷ A.scheme).left DA.poincare) :=
  normalized_family_pullback A (DualComparison.dualMap DA DB f) DA.poincare DA.normalizedAtAbelianZero

def abelianLocalBundle (f : A.scheme ⟶ B.scheme) {T : Over S}
    (t : T ⟶ DB.abelian.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (t ▷ A.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DB.abelian.scheme ◁ f).left DB.poincare)

def dualLocalBundle (f : A.scheme ⟶ B.scheme) [IsMonHom f] {T : Over S}
    (t : T ⟶ DB.abelian.scheme) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (t ▷ A.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DualComparison.dualMap DA DB f ▷ A.scheme).left DA.poincare)

def abelianGlobalZeroIso (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (familyZero A DB.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DB.abelian.scheme ◁ f).left DB.poincare)).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule DB.abelian.scheme.left :=
  Classical.choice (abelianPull_normalized DB f)

def dualGlobalZeroIso (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (familyZero A DB.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (DualComparison.dualMap DA DB f ▷ A.scheme).left DA.poincare)).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule DB.abelian.scheme.left :=
  Classical.choice (dualPull_normalized DA DB f)

def abelianLocalZeroIso (f : A.scheme ⟶ B.scheme) [IsMonHom f] {T : Over S}
    (t : T ⟶ DB.abelian.scheme) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (familyZero A T).left (abelianLocalBundle DB f t)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
  familyPullbackZeroIso A t _ (abelianGlobalZeroIso DB f)

def dualLocalZeroIso (f : A.scheme ⟶ B.scheme) [IsMonHom f] {T : Over S}
    (t : T ⟶ DB.abelian.scheme) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (familyZero A T).left (dualLocalBundle DA DB f t)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
  familyPullbackZeroIso A t _ (dualGlobalZeroIso DA DB f)

/-- The actual normalized isomorphism on every member of the cover
constructed from representability. -/
def normalizedPoincareLocalIso (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t) :
    (abelianLocalBundle DB f t).sheaf ≅ (dualLocalBundle DA DB f t).sheaf :=
  RigidifiedIso.normalizedIso (fst T A.scheme).left (familyZero A T).left
    (PoincareLocal.poincareLocalIso DA DB f t ht) (abelianLocalZeroIso DB f t) (dualLocalZeroIso DA DB f t)

theorem normalizedPoincareLocalIso_section (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} (t : T ⟶ DB.abelian.scheme)
    (ht : (PoincareLocal.poincareComparisonCover DA DB f).1 t) :
    (Scheme.Modules.pullback (familyZero A T).left).map
        (normalizedPoincareLocalIso DA DB f t ht).hom ≫ (dualLocalZeroIso DA DB f t).hom =
      (abelianLocalZeroIso DB f t).hom :=
  RigidifiedIso.normalizedIso_section (fst T A.scheme).left (familyZero A T).left
    (familyZero_projection A T) (PoincareLocal.poincareLocalIso DA DB f t ht)
    (abelianLocalZeroIso DB f t) (dualLocalZeroIso DA DB f t)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
