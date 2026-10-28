import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.Gluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.RigidityLocallyNoetherian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseSquareIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackLevelCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveryFromPullbackIso

/-! # Polarized Scheme Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing

noncomputable section

/-! At full level at least three, original polarized chart isomorphisms
supply coherent Cartesian diagrams for both abelian schemes. The coherence
is proved from original full-level rigidity over the Noetherian chart
bases; it is not supplied as a descent assumption. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

attribute [local instance] Gluing.nativePullbackGroup

private theorem total_composition {C : Type*} [Category* C]
    {A B P Q R T U : C}
    (a : A ⟶ B) (b : B ⟶ P) (c : P ⟶ Q) (d : Q ⟶ U)
    (p : P ⟶ R) (q : R ⟶ U) (r : B ⟶ T) (s : T ⟶ R)
    (hc : c ≫ d = p ≫ q) (hb : b ≫ p = r ≫ s) :
    ((a ≫ b) ≫ c) ≫ d = (a ≫ r) ≫ (s ≫ q) := by
  rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc, Category.assoc a b p,
    hb]
  simp only [Category.assoc]

namespace LevelPreservingIso
variable {S T V : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
  {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
  {B : PolarizationData.PolarizedAbelianWithFullLevel g δ N T}
  {E : PolarizationData.PolarizedAbelianWithFullLevel g δ N V}

/-- The actual total-space morphism associated to a family isomorphism. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.abelianTotal (f : S ⟶ T) (e : Moduli.Isomorphisms.LevelPreservingIso A (B.pullback f)) :
    A.abelian.scheme.left ⟶ B.abelian.scheme.left :=
  e.abelian.hom.left ≫ pullback.fst B.abelian.scheme.hom f

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.dualTotal (f : S ⟶ T) (e : Moduli.Isomorphisms.LevelPreservingIso A (B.pullback f)) :
    A.dual.abelian.scheme.left ⟶ B.dual.abelian.scheme.left :=
  e.dual.hom.left ≫ pullback.fst B.dual.abelian.scheme.hom f

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.abelianTotal_congr (f h : S ⟶ T) (w : f = h)
    (e : Moduli.Isomorphisms.LevelPreservingIso A (B.pullback f)) :
    Moduli.Isomorphisms.LevelPreservingIso.abelianTotal h (e.trans (Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps B f h w)) = Moduli.Isomorphisms.LevelPreservingIso.abelianTotal f e := by
  subst h
  change (e.abelian.hom.left ≫ 𝟙 _) ≫ pullback.fst B.abelian.scheme.hom f =
    e.abelian.hom.left ≫ pullback.fst B.abelian.scheme.hom f
  rw [Category.comp_id]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.dualTotal_congr (f h : S ⟶ T) (w : f = h)
    (e : Moduli.Isomorphisms.LevelPreservingIso A (B.pullback f)) :
    Moduli.Isomorphisms.LevelPreservingIso.dualTotal h (e.trans (Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps B f h w)) = Moduli.Isomorphisms.LevelPreservingIso.dualTotal f e := by
  subst h
  change (e.dual.hom.left ≫ 𝟙 _) ≫ pullback.fst B.dual.abelian.scheme.hom f =
    e.dual.hom.left ≫ pullback.fst B.dual.abelian.scheme.hom f
  rw [Category.comp_id]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.abelianTotal_identity :
    Moduli.Isomorphisms.LevelPreservingIso.abelianTotal (𝟙 S) (Moduli.Isomorphisms.LevelPreservingIso.pullbackId A).symm = 𝟙 A.abelian.scheme.left := by
  change A.abelian.pullbackIdIso.inv.left ≫ pullback.fst A.abelian.scheme.hom (𝟙 S) = _
  rw [← A.abelian.pullbackIdIso_hom_left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.dualTotal_identity :
    Moduli.Isomorphisms.LevelPreservingIso.dualTotal (𝟙 S) (Moduli.Isomorphisms.LevelPreservingIso.pullbackId A).symm = 𝟙 A.dual.abelian.scheme.left := by
  change A.dual.abelian.pullbackIdIso.inv.left ≫
    pullback.fst A.dual.abelian.scheme.hom (𝟙 S) = _
  rw [← A.dual.abelian.pullbackIdIso_hom_left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.abelianTotal_composition (f : S ⟶ T) (h : T ⟶ V)
    (e : Moduli.Isomorphisms.LevelPreservingIso A (B.pullback f))
    (d : Moduli.Isomorphisms.LevelPreservingIso B (E.pullback h)) :
    Moduli.Isomorphisms.LevelPreservingIso.abelianTotal (f ≫ h) ((e.trans (d.pullback f)).trans (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp E h f)) =
      Moduli.Isomorphisms.LevelPreservingIso.abelianTotal f e ≫ Moduli.Isomorphisms.LevelPreservingIso.abelianTotal h d :=
  total_composition _ _ _ _ _ _ _ _
    (E.abelian.pullbackCompIso_inv_left_fst h f)
    (Pullback.Comparisons.overPullback_map_left_fst d.abelian.hom f)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.dualTotal_composition (f : S ⟶ T) (h : T ⟶ V)
    (e : Moduli.Isomorphisms.LevelPreservingIso A (B.pullback f))
    (d : Moduli.Isomorphisms.LevelPreservingIso B (E.pullback h)) :
    Moduli.Isomorphisms.LevelPreservingIso.dualTotal (f ≫ h) ((e.trans (d.pullback f)).trans (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp E h f)) =
      Moduli.Isomorphisms.LevelPreservingIso.dualTotal f e ≫ Moduli.Isomorphisms.LevelPreservingIso.dualTotal h d :=
  total_composition _ _ _ _ _ _ _ _
    (E.dual.abelian.pullbackCompIso_inv_left_fst h f)
    (Pullback.Comparisons.overPullback_map_left_fst d.dual.hom f)

end LevelPreservingIso

/-- Recovering a specified native pullback isomorphism from its own
Cartesian total-space square returns the original isomorphism. -/
theorem cartesianAmbientOverIso_of_iso {S T : Scheme.{u}} (f : S ⟶ T)
    {X : Over S} {Y : Over T} (e : X ≅ (Over.pullback f).obj Y) :
    ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (e.hom.left ≫ pullback.fst Y.hom f) f
      (RecoveryFromPullbackIso.schemeRecovery_isPullback_of_overIso f e) = e := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (RecoveryFromPullbackIso.schemeRecovery_isPullback_of_overIso f e).isoPullback_hom_fst
  · exact (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (e.hom.left ≫ pullback.fst Y.hom f) f
      (RecoveryFromPullbackIso.schemeRecovery_isPullback_of_overIso f e)).hom.w.trans e.hom.w.symm

private theorem cartesianAmbientOverIso_of_iso_group {S T : Scheme.{u}} (f : S ⟶ T)
    {X : Over S} {Y : Over T} [GrpObj X] [GrpObj Y]
    (e : X ≅ (Over.pullback f).obj Y) [IsMonHom e.hom] :
    IsMonHom (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (e.hom.left ≫ pullback.fst Y.hom f) f
      (RecoveryFromPullbackIso.schemeRecovery_isPullback_of_overIso f e)).hom := by
  rw [cartesianAmbientOverIso_of_iso]
  infer_instance

namespace DirectedPolarizedSchemeGluing
variable {S : Scheme.{u}} (C : S.OpenCover.{u})
  [Category C.I₀] [C.LocallyDirected] [Small.{u} C.I₀] [Quiver.IsThin C.I₀]
  [∀ i, IsLocallyNoetherian (C.X i)] {g N : ℕ} {δ : Fin g → ℕ}
  (F : ∀ i, PolarizationData.PolarizedAbelianWithFullLevel g δ N (C.X i)) (hN : 3 ≤ N)
  (e : ∀ {i j : C.I₀} (f : i ⟶ j), Moduli.Isomorphisms.LevelPreservingIso (F i) ((F j).pullback (C.trans f)))

private def identityComparison (i : C.I₀) :
    Moduli.Isomorphisms.LevelPreservingIso (F i) ((F i).pullback (C.trans (𝟙 i))) :=
  (Moduli.Isomorphisms.LevelPreservingIso.pullbackId (F i)).symm.trans
    (Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps (F i) (𝟙 (C.X i)) (C.trans (𝟙 i)) (C.trans_id i).symm)

private def compositeComparison {i j k : C.I₀} (f : i ⟶ j) (h : j ⟶ k) :
    Moduli.Isomorphisms.LevelPreservingIso (F i) ((F k).pullback (C.trans (f ≫ h))) :=
  (((e f).trans ((e h).pullback (C.trans f))).trans
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp (F k) (C.trans h) (C.trans f))).trans
      (Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps (F k) (C.trans f ≫ C.trans h)
        (C.trans (f ≫ h)) (C.trans_comp f h).symm)

include hN in
omit [Small.{u} C.I₀] [Quiver.IsThin C.I₀] in
private theorem identity_eq (i : C.I₀) : e (𝟙 i) = identityComparison C F i := by
  let := Level.RigidityLocallyNoetherian.polarizedIsomorphisms_subsingleton_of_locallyNoetherian
    (F i) ((F i).pullback (C.trans (𝟙 i))) hN
  exact Subsingleton.elim _ _

include hN in
omit [Small.{u} C.I₀] [Quiver.IsThin C.I₀] in
private theorem composite_eq {i j k : C.I₀} (f : i ⟶ j) (h : j ⟶ k) :
    e (f ≫ h) = compositeComparison C F e f h := by
  let := Level.RigidityLocallyNoetherian.polarizedIsomorphisms_subsingleton_of_locallyNoetherian
    (F i) ((F k).pullback (C.trans (f ≫ h))) hN
  exact Subsingleton.elim _ _

/-- Abelian total spaces with their original Cartesian group transitions. -/
def abelianData : Gluing.DirectedAbelianGluingData C g where
  family i := (F i).abelian
  transition f := Moduli.Isomorphisms.LevelPreservingIso.abelianTotal (C.trans f) (e f)
  transition_id i := by
    rw [identity_eq C F hN e i]
    exact (Moduli.Isomorphisms.LevelPreservingIso.abelianTotal_congr _ _ _ _).trans
      (Moduli.Isomorphisms.LevelPreservingIso.abelianTotal_identity (A := F i))
  transition_comp f h := by
    rw [composite_eq C F hN e f h]
    exact (Moduli.Isomorphisms.LevelPreservingIso.abelianTotal_congr _ _ _ _).trans
      (Moduli.Isomorphisms.LevelPreservingIso.abelianTotal_composition (C.trans f) (C.trans h) (e f) (e h))
  cartesian f := RecoveryFromPullbackIso.schemeRecovery_isPullback_of_overIso (C.trans f) (e f).abelian
  group {i j} f := by
    let ef : (F i).abelian.scheme ≅ (Over.pullback (C.trans f)).obj (F j).abelian.scheme :=
      (e f).abelian
    let : IsMonHom ef.hom := (e f).abelianGroup
    exact cartesianAmbientOverIso_of_iso_group (C.trans f) ef

/-- The dual total spaces glue separately with the original dual group maps. -/
def dualData : Gluing.DirectedAbelianGluingData C g where
  family i := (F i).dual.abelian
  transition f := Moduli.Isomorphisms.LevelPreservingIso.dualTotal (C.trans f) (e f)
  transition_id i := by
    rw [identity_eq C F hN e i]
    exact (Moduli.Isomorphisms.LevelPreservingIso.dualTotal_congr _ _ _ _).trans
      (Moduli.Isomorphisms.LevelPreservingIso.dualTotal_identity (A := F i))
  transition_comp f h := by
    rw [composite_eq C F hN e f h]
    exact (Moduli.Isomorphisms.LevelPreservingIso.dualTotal_congr _ _ _ _).trans
      (Moduli.Isomorphisms.LevelPreservingIso.dualTotal_composition (C.trans f) (C.trans h) (e f) (e h))
  cartesian f := RecoveryFromPullbackIso.schemeRecovery_isPullback_of_overIso (C.trans f) (e f).dual
  group {i j} f := by
    let ef : (F i).dual.abelian.scheme ≅ (Over.pullback (C.trans f)).obj (F j).dual.abelian.scheme :=
      (e f).dual
    let : IsMonHom ef.hom := (e f).dualGroup
    exact cartesianAmbientOverIso_of_iso_group (C.trans f) ef

def abelian : Abelian.Schemes.AbelianScheme g S := (abelianData C F hN e).abelian

def dualAbelian : Abelian.Schemes.AbelianScheme g S := (dualData C F hN e).abelian

def abelianChartIso (i : C.I₀) : (F i).abelian.scheme ≅ ((DirectedPolarizedSchemeGluing.abelian C F hN e).pullback (C.f i)).scheme :=
  (abelianData C F hN e).chartIso i

def dualChartIso (i : C.I₀) : (F i).dual.abelian.scheme ≅ ((dualAbelian C F hN e).pullback (C.f i)).scheme :=
  (dualData C F hN e).chartIso i

instance abelianChartIso_group (i : C.I₀) : IsMonHom (abelianChartIso C F hN e i).hom :=
  (abelianData C F hN e).chartIso_preservesGroup i

instance dualChartIso_group (i : C.I₀) : IsMonHom (dualChartIso C F hN e i).hom :=
  (dualData C F hN e).chartIso_preservesGroup i

end DirectedPolarizedSchemeGluing

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing
