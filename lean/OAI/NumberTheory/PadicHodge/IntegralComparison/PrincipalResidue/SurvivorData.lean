import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.TopCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOneHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCompositeHomology

/-! # Survivor Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorData

noncomputable section

/-! The actual principal residue on the surviving homology sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

def map : Principal.SectionPresheaf.modules U hU ((Affine.LinearResolutionPurity.internalComplex N K).homology c) ⟶
    Principal.ClosedKoszulResidue.target f U hU :=
  (Principal.ModuleHomology.complexIso U hU
    (Affine.LinearResolutionPurity.internalComplex N K) c).inv ≫
  homologyMap (Principal.OrientedResidue.map f U hU N e K ε s hs hreg) c ≫
  (singleObjHomologySelfIso (.up ℕ) c (Principal.ClosedKoszulResidue.target f U hU)).hom

def normalized : (Affine.ModuleExactSections.sections U).obj
    ((Affine.LinearResolutionPurity.internalComplex N K).homology c) ⟶
    ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s) :=
  ((Principal.AtOne.iso U hU).app
      ((Affine.LinearResolutionPurity.internalComplex N K).homology c)).hom ≫
    (map U hU N e K f ε s hs hreg).app (op (Principal.AtOne.object U)) ≫
    (Principal.OrientedResidueNormalization.targetAtOne U hU f s hs).hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorData
