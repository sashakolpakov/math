import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorData

/-! # Survivor Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorCoordinates

noncomputable section

/-! The actual residue on the homology sheaf has the original
oriented-purity coordinate at the unit principal open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem join {C : Type*} [Category C] {S A B D E V W : C}
    (u : S ⟶ A) (i : A ⟶ B) (r : B ⟶ D) (t : D ⟶ E)
    (h : S ⟶ V) (v : V ⟶ W) (w : W ⟶ B) (m : V ⟶ E)
    (hu : u ≫ i = h ≫ v ≫ w) (hm : m = v ≫ w ≫ r ≫ t) :
    u ≫ (i ≫ r) ≫ t = h ≫ m := by
  rw [hm]
  calc
    _ = (u ≫ i) ≫ r ≫ t := by simp only [Category.assoc]
    _ = _ := by rw [hu]; simp only [Category.assoc]

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj (Principal.ClosedQuotient.directImage f))
  [QuasiIso ε] [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]

attribute [local instance] Principal.OrientedResidue.structure_quasicoherent

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LinearResolutionPurity.internalComplex N K
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Koszul.Comparison.nativeComplex U hU N K
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization.atOneFunctor U
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedKoszulResidue.target f U hU
local notation "q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue.map f U hU N e K ε s hs hreg
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalizationBase.sourceAtOneIso U hU N K
local notation "t" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization.targetAtOne U hU f s hs

omit [∀ k, ((Affine.LinearResolutionPurity.internalComplex N K).X k).IsQuasicoherent] in
theorem evaluation_homology :
    homologyMap (Principal.OrientedResidueNormalization.normalizedMap
      U hU N e K f ε s hs hreg) c ≫
        (singleObjHomologySelfIso (.up ℕ) c
          (ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s))).hom =
      homologyMap (a).hom c ≫
        (Principal.AtOneHomology.evaluationIso U hU A c).hom ≫
          (E).map (homologyMap q c ≫ (singleObjHomologySelfIso (.up ℕ) c Q).hom) ≫ (t).hom :=
  Mapped.SingleCompositeHomology.homology_expanded E T Q c q _ (a).hom _ (t).hom

omit [N.IsQuasicoherent] [∀ k, (K.X k).IsQuasicoherent]
  [∀ k, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X k))] in
theorem source_homology :
    ((Principal.AtOne.iso U hU).app ((A).homology c)).hom ≫
      (Principal.ModuleHomology.complexIso U hU A c).inv.app (op (Principal.AtOne.object U)) =
    (Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K c).hom ≫
      homologyMap (a).hom c ≫ (Principal.AtOneHomology.evaluationIso U hU A c).hom :=
  Principal.AtOneHomology.square U hU A c

theorem normalized_homology :
    SurvivorData.normalized U hU N e K f ε s hs hreg =
      (Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K c).hom ≫
        homologyMap (Principal.OrientedResidueNormalization.normalizedMap
          U hU N e K f ε s hs hreg) c ≫
          (singleObjHomologySelfIso (.up ℕ) c
            (ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s))).hom :=
  join _ _ ((E).map (homologyMap q c ≫ (singleObjHomologySelfIso (.up ℕ) c Q).hom))
    (t).hom _ (homologyMap (a).hom c) _ _
    (source_homology U hU N K (c := c))
    (evaluation_homology U hU N e K f ε s hs hreg)

theorem comparison : SurvivorData.normalized U hU N e K f ε s hs hreg =
    (Affine.OrientedPurity.iso U hU N K (Principal.ClosedQuotient.directImage f) ε
      (KoszulPartial.Resolution.normalIdeal Γ(Y, U) s)
      (Principal.OrientedResidue.quotientIso f U hU s hs) s rfl hreg
      (Principal.OrientedResidueNormalizationBase.lineIso U hU N e)).hom :=
  (normalized_homology U hU N e K f ε s hs hreg).trans
    (TopCoordinates.OrientedNormalization.comparison U hU N e K f ε s hs hreg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorCoordinates
