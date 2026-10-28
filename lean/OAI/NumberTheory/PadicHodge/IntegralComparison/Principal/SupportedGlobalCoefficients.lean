import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.GlobalCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedCover

/-! # Supported Global Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedGlobalCoefficients

noncomputable section

/-! The exact coefficient-global principal square ends in the
original map forgetting support, and remains so after any target map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v z uB vB
variable (R : Type u) [CommRing R] (X : TopCat.{v})

local instance coefficient_limits [UnivLE.{v,z}] : HasLimitsOfSize.{v,v} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{v,v,z,u}
local instance coefficient_products [UnivLE.{v,z}] : HasProducts.{v} (ModuleCat.{z} R) :=
  fun J => by
    let : HasLimitsOfSize.{v,v} (ModuleCat.{z} R) := ModuleCat.hasLimitsOfSize.{v,v,z,u}
    exact HasLimitsOfSize.has_limits_of_shape (Discrete J)
local instance coefficient_biproducts : HasFiniteBiproducts (ModuleCat.{z} R) :=
  Abelian.hasFiniteBiproducts
local instance coefficient_coproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun J => by
    let : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) := ModuleCat.hasColimitsOfSize.{z,u,0,0} R
    exact HasColimitsOfSize.has_colimits_of_shape (Discrete J)

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v z} R)) ℕ)
  {C : Type v} [Preorder C] [HasFiniteProducts C] (F : C ⥤ Opens X)
  {ι κ ν μ ρ : Type v}
  [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (W : ι → C)
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) F]
  (B₀ : κ → Opens X) (J : ν → Opens X)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι (F.obj ∘ W))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B₀)
  (V : μ → Opens X) (T : ρ → Opens X)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover (F.obj (⊤_ C)) B₀))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (O : Opens X) (hW : ∀ i, F.obj (W i) ≤ O) (hB : ∀ i, B₀ i ≤ O)
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology (F.obj (⊤_ C)) B₀ J s
    (Relative.SupportedExtension.underlying.{u,v,z} R X K) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
    (Relative.SupportedExtension.underlying.{u,v,z} R X K)) q)]
  [IsIso (homologyMap (Presheaf.OrderedCechEdge.edge V
    (Relative.SupportedExtension.underlying.{u,v,z} R X K)) q)]
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (W i))
  (hrows : ∀ n m, ((Supported.OrderedCechEdge.bicomplex.{u,v,v,z} R X F W K).X n).ExactAt (m+1))

include hB in
theorem forget_comparison :
    PresheafCover.Comparison.comparison F W B₀ J r s V T l t
        (Relative.SupportedExtension.underlying.{u,v,z} R X K) q ≫
      inv (homologyMap (Presheaf.OrderedCechEdge.edge V
        (Relative.SupportedExtension.underlying.{u,v,z} R X K)) q) =
    Supported.OrderedCech.Comparison.forgetSupport.{u,v,v,z}
      R X F W O K hW hcover hrows hglobal q := by
  rw [SupportedCover.Comparison.comparison R X K F W B₀ J r s V T l t
    O hW hB hglobal q hcover hrows]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasProducts.{v} B] [HasCoproducts.{0} B]
  (G : ModuleCat.{max u v z} R ⥤ B) [G.Additive] [G.PreservesHomology]
  [PreservesLimitsOfSize.{v,v} G]

abbrev comparison :=
  (GlobalCoefficients.comparison G
    (Relative.SupportedExtension.underlying.{u,v,z} R X K) F W B₀ J r s V T l t q).trans
    (congrArg G.map (forget_comparison R X K F W B₀ J r s V T l t O hW hB hglobal q hcover hrows))

abbrev with_target (Z : ModuleCat.{max u v z} R)
    (a : (Presheaf.OrderedCechEdge.sections
      (Relative.SupportedExtension.underlying.{u,v,z} R X K)).homology q ⟶ Z) :=
  (congrArg (fun f => f ≫ G.map a)
    (comparison R X K F W B₀ J r s V T l t O hW hB hglobal q hcover hrows G)).trans
      (G.map_comp
        (Supported.OrderedCech.Comparison.forgetSupport.{u,v,v,z}
          R X F W O K hW hcover hrows hglobal q) a).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedGlobalCoefficients
