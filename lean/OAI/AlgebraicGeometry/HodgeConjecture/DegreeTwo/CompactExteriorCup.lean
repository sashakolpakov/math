import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupNaturality
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit

/-! # Compact Exterior Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactExteriorCup.Constructions

noncomputable section

section

/-!
# DegreeTwo: actual exterior cup on compact-support stages

The product of compact supports is compact. The previously constructed
supported exterior cup therefore gives an actual compact-support class,
with linearity in both inputs and no choice of representatives.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit

set_option backward.isDefEq.respectTransparency false

variable (X Y : TopCat.{0})

def relativeExteriorCupBilinear (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p →ₗ[ℚ]
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q →ₗ[ℚ]
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
          (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p+q)) where
  toFun a := (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X×Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
    (hA.preimage continuous_fst) (hB.preimage continuous_snd) p q
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst : TopCat.of (X×Y) ⟶ X)
      (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p a)).comp
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodSnd : TopCat.of (X×Y) ⟶ Y)
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q).hom
  map_add' a b := by ext c; simp only [map_add,LinearMap.comp_apply,LinearMap.add_apply]
  map_smul' r a := by ext c; simp only [map_smul,LinearMap.comp_apply,LinearMap.smul_apply,RingHom.id_apply]

theorem relativeExteriorCupBilinear_apply (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (p q : ℕ) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q) :
    relativeExteriorCupBilinear X Y A B hA hB p q a b =
      ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a b := rfl

theorem compactProductComplement (K : Compacts X) (L : Compacts Y) :
    RelativeCrossSupport.Constructions.crossSupportComplement X Y (K : Set X)ᶜ (L : Set Y)ᶜ =
      ((K ×ˢ L : Compacts (X×Y)) : Set (X×Y))ᶜ := by
  ext z
  simp only [RelativeCrossSupport.Constructions.crossSupportComplement, Set.mem_union, Set.mem_preimage, Set.mem_compl_iff,
    Compacts.coe_prod, Set.mem_prod, not_and_or]

variable [T2Space X] [T2Space Y]

def compactExteriorCupStage (K : Compacts X) (L : Compacts Y) (p q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p →ₗ[ℚ]
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q →ₗ[ℚ]
        AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (p+q)) where
  toFun a := ((AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
      (K ×ˢ L) (p+q)).hom.comp
    (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (X×Y)) S (p+q)) (compactProductComplement X Y K L))).hom).comp
    (relativeExteriorCupBilinear X Y (K : Set X)ᶜ (L : Set Y)ᶜ
      K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl p q a)
  map_add' a b := by ext c; simp only [map_add,LinearMap.comp_apply,LinearMap.add_apply]
  map_smul' r a := by ext c; simp only [map_smul,LinearMap.comp_apply,LinearMap.smul_apply,RingHom.id_apply]

theorem compactExteriorCupStage_apply (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q) :
    compactExteriorCupStage X Y K L p q a b =
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (K ×ˢ L) (p+q)
        (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
          (TopCat.of (X×Y)) S (p+q)) (compactProductComplement X Y K L))
          (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y (K : Set X)ᶜ (L : Set Y)ᶜ
            K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl p q a b)) := rfl

end

section

/-! The actual compact exterior-cup stages commute with enlargement of both supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit

set_option backward.isDefEq.respectTransparency false

theorem relativeSupportCast_naturality (X : TopCat.{0}) {S T S' T' : Set X}
    (hs : S = S') (ht : T = T') (h : T ⊆ S) (h' : T' ⊆ S') (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) (fun _ hx => h' hx) n
      (eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) hs) a) =
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) ht)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) (fun _ hx => h hx) n a) := by
  subst S' T'
  rfl

theorem relativeExteriorCup_support_naturality (X Y : TopCat.{0})
    {A A' : Set X} {B B' : Set Y} (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hoA : IsOpen A) (hoB : IsOpen B) (hoA' : IsOpen A') (hoB' : IsOpen B') (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q) :
    ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A' B' hoA' hoB' p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) (fun _ hx => hA hx) p a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 Y) (fun _ hx => hB hx) q b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (X×Y)))
      (A := RelativeCrossSupport.Constructions.crossSupportComplement X Y A' B') (B := RelativeCrossSupport.Constructions.crossSupportComplement X Y A B)
      (fun _ hx => hx.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h))) (p+q)
      (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hoA hoB p q a b) :=
  ExteriorCupNaturality.Constructions.relativeExteriorCup_naturality (𝟙 X) (𝟙 Y) (fun _ hx => hA hx) (fun _ hx => hB hx)
    hoA' hoB' hoA hoB p q a b

variable (X Y : TopCat.{0}) [T2Space X] [T2Space Y]

theorem compactExteriorCupStage_naturality
    {K K' : Compacts X} {L L' : Compacts Y} (hK : K ≤ K') (hL : L ≤ L') (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q) :
    compactExteriorCupStage X Y K' L' p q
      (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) hK p a)
      (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) hL q b) =
      compactExteriorCupStage X Y K L p q a b := by
  have hP : (K ×ˢ L : Compacts (X×Y)) ≤ K' ×ˢ L' := fun _ hx => ⟨hK hx.1,hL hx.2⟩
  have hKc : (K' : Set X)ᶜ ⊆ (K : Set X)ᶜ := fun _ hx h => hx (hK h)
  have hLc : (L' : Set Y)ᶜ ⊆ (L : Set Y)ᶜ := fun _ hx h => hx (hL h)
  have hS : RelativeCrossSupport.Constructions.crossSupportComplement X Y (K' : Set X)ᶜ (L' : Set Y)ᶜ ⊆
      RelativeCrossSupport.Constructions.crossSupportComplement X Y (K : Set X)ᶜ (L : Set Y)ᶜ :=
    fun _ hx => hx.elim (fun h => Or.inl (hKc h)) (fun h => Or.inr (hLc h))
  have hPc : ((K' ×ˢ L' : Compacts (X×Y)) : Set (X×Y))ᶜ ⊆
      ((K ×ˢ L : Compacts (X×Y)) : Set (X×Y))ᶜ := fun _ hx h => hx (hP h)
  have hc := relativeExteriorCup_support_naturality X Y hKc hLc
    K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl
    K'.isCompact.isClosed.isOpen_compl L'.isCompact.isClosed.isOpen_compl p q a b
  change ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y (K' : Set X)ᶜ (L' : Set Y)ᶜ _ _ p q
    (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) hK p a)
    (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) hL q b) = _ at hc
  have ht := relativeSupportCast_naturality (TopCat.of (X×Y))
    (compactProductComplement X Y K L) (compactProductComplement X Y K' L') hS hPc (p+q)
    (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y (K : Set X)ᶜ (L : Set Y)ᶜ
      K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl p q a b)
  rw [compactExteriorCupStage_apply, hc, ← ht]
  change (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) hP (p+q) ≫
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (K' ×ˢ L') (p+q)) _ = _
  rw [AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_ι]
  rfl

end

/-!
# DegreeTwo: exterior cup on actual compactly supported cohomology

The two genuine compact-support colimits descend the supported exterior cup.
The stage formula retains the actual relative cup and its support.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportColimit

set_option backward.isDefEq.respectTransparency false

variable (X Y : TopCat.{0}) [T2Space X] [T2Space Y]

def compactExteriorCupLeftDesc (L : Compacts Y) (p q : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p →ₗ[ℚ]
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q →ₗ[ℚ]
        AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (p+q)) :=
  (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) X p
    (fun K => ModuleCat.ofHom (compactExteriorCupStage X Y K L p q))
    (fun K K' h => by
      ext a b
      change compactExteriorCupStage X Y K' L p q
        (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h p a) b =
        compactExteriorCupStage X Y K L p q a b
      have hc := compactExteriorCupStage_naturality X Y h (le_refl L) p q a b
      simpa only [AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_refl, ModuleCat.id_apply] using hc)).hom

theorem compactExteriorCupLeftDesc_stage (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q) :
    compactExteriorCupLeftDesc X Y L p q
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K p a) b =
      compactExteriorCupStage X Y K L p q a b := by
  exact congrArg (fun f : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q →ₗ[ℚ]
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (p+q) => f b)
    (ConcreteCategory.congr_hom
    (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyι_desc (ModuleCat.of ℚ ℚ) X p _ _ K) a)

theorem compactExteriorCupLeftDesc_naturality {L L' : Compacts Y} (h : L ≤ L') (p q : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q) :
    compactExteriorCupLeftDesc X Y L' p q a
      (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h q b) =
      compactExteriorCupLeftDesc X Y L p q a b := by
  obtain ⟨K,c,rfl⟩ := AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ) X p a
  rw [compactExteriorCupLeftDesc_stage, compactExteriorCupLeftDesc_stage]
  have hc := compactExteriorCupStage_naturality X Y (le_refl K) h p q c b
  simpa only [AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_refl, ModuleCat.id_apply] using hc

def compactExteriorCup (p q : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p →ₗ[ℚ]
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) Y q →ₗ[ℚ]
        AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (p+q)) :=
  LinearMap.flip (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) Y q
    (fun L => ModuleCat.ofHom (LinearMap.flip (compactExteriorCupLeftDesc X Y L p q)))
    (fun L L' h => by
      ext b a
      exact compactExteriorCupLeftDesc_naturality X Y h p q a b)).hom

theorem compactExteriorCup_stage (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q) :
    compactExteriorCup X Y p q
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K p a)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) Y L q b) =
      compactExteriorCupStage X Y K L p q a b := by
  unfold compactExteriorCup
  have hf : ∀ L L' (h : L ≤ L'),
      AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h q ≫
        ModuleCat.ofHom (LinearMap.flip (compactExteriorCupLeftDesc X Y L' p q)) =
        ModuleCat.ofHom (LinearMap.flip (compactExteriorCupLeftDesc X Y L p q)) := by
    intro L L' h
    ext b a
    exact compactExteriorCupLeftDesc_naturality X Y h p q a b
  have hb := congrArg
    (fun f : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X p →ₗ[ℚ]
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (p+q) =>
      f (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K p a))
    (ConcreteCategory.congr_hom
      (AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyι_desc (ModuleCat.of ℚ ℚ) Y q
        (fun L => ModuleCat.ofHom (LinearMap.flip (compactExteriorCupLeftDesc X Y L p q))) hf L) b)
  exact hb.trans (compactExteriorCupLeftDesc_stage X Y K L p q a b)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactExteriorCup.Constructions
