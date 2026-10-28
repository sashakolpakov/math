import OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalLocal
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportDetection
import OAI.AlgebraicGeometry.CycleClass.Thom.BoundedAffineNormalizationGraph

/-! # Cup Principal Detection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalDetection.Constructions

noncomputable section

/-! Local bounded normalization formulas determine the two canonical
classes on every analytic open whose support points avoid the actual
exceptional boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalLocal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero.Constructions.BoundaryUnion
open OAI.AlgebraicGeometry.CycleClass.Thom.BoundedAffineNormalizationGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) (hB : B ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val)
  [Nonempty B] [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] [IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  (hgood : ∀ x : U, V.analyticUnderlying x.val ∈ ClosedSupport.Constructions.sectionClosedSupport D B s →
    x.val ∈ Normalization.PrincipalZero.Constructions.BoundaryUnion.commonOpen V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left := inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)

local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D B s
local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V D.val + 1
local notation "I" => Subtype (fun x : U => V.analyticUnderlying (Subtype.val x) ∈ F)

include hB hgood in
theorem sectionCupClass_eq_principal_on_retained_open :
    Cup.Constructions.Class.sectionCupClass D B s U hU = Principal.Constructions.Class.sectionPrincipalClass D B s hs U := by
  classical
  have hA : IsAffineOpen B := inferInstanceAs (IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left)
  let : IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left := Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource_affine D B hA
  have hlocal : ∀ x : I, ∃ (P : Opens V.analyticSpace) (hPU : P ≤ U),
      x.val.val ∈ P ∧ Cup.Constructions.Class.sectionCupClass D B s P (fun _ hz => hU (hPU hz)) = Principal.Constructions.Class.sectionPrincipalClass D B s hs P := by
    intro x
    obtain ⟨y, hy⟩ := hU x.val.property
    obtain ⟨d, f, U₀, K, hf, hclosed, hy₀, _, hK, _, hb⟩ :=
      BoundedAffineNormalizationGraph.Constructions.exists_bounded_affine_normalization_graph D B hB hA y
    let : IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B) f).left := hclosed
    let P := U ⊓ U₀ ⊓ Normalization.PrincipalZero.Constructions.BoundaryUnion.commonOpen V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs
    have hPU : P ≤ U := fun _ hz => hz.1.1
    refine ⟨P, hPU, ⟨⟨x.val.property, hy ▸ hy₀⟩, hgood x.val x.property⟩, ?_⟩
    exact CupPrincipalLocal.Constructions.sectionCupClass_eq_principal_bounded D B hB s hs P (fun _ hz => hU (hPU hz))
      (fun _ hz => hz.2) d f hf K hK (fun y hyP => hb y hyP.1.2)
  choose P hPU hxP hEq using hlocal
  apply Scheme.OpenSupportDetection.Constructions.relativeClass_eq_of_support_neighborhoods V.toOver F q
    (ClosedSupport.Constructions.sectionClosedSupport_dimension D B s hs) U P hPU hxP
  intro x
  exact (CupRestriction.Constructions.sectionCupClass_restrict D B s U (P x) (hPU x) hU (fun _ hz => hU (hPU x hz))).trans
    ((hEq x).trans (Principal.Constructions.Class.sectionPrincipalClass_restrict D B s hs U (P x) (hPU x)).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalDetection.Constructions
