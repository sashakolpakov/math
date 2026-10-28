import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkMap
import OAI.AlgebraicGeometry.Comparison.Betti.NoetherianHolomorphicGerms

/-! # Stalk Germs -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkGerms.AnalyticLocal

noncomputable section

/-! The actual holomorphic function sheaf stalk is the holomorphic germ
ring and is therefore Noetherian in finite dimensions. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite Set Filter
open scoped _root_.Topology

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem holomorphicStalkToGerm_injective (x : E) : Function.Injective (StalkMap.AnalyticLocal.holomorphicStalkToGerm E x) := by
  intro a b hab
  obtain ⟨U, hxU, f, rfl⟩ := (FunctionSheaf.holomorphicFunctionPresheaf E).exists_germ_eq a
  obtain ⟨V, hxV, g, rfl⟩ := (FunctionSheaf.holomorphicFunctionPresheaf E).exists_germ_eq b
  have hab' : SectionGerms.AnalyticLocal.holomorphicSectionGerm U x hxU f = SectionGerms.AnalyticLocal.holomorphicSectionGerm V x hxV g :=
    (StalkMap.AnalyticLocal.holomorphicStalkToGerm_germ_apply E x U hxU f).symm.trans
      (hab.trans (StalkMap.AnalyticLocal.holomorphicStalkToGerm_germ_apply E x V hxV g))
  have he := congrArg Subtype.val hab'
  change (CoefficientMem.openCoefficientExtension U f.val : Germ (𝓝 x) ℂ) =
    (CoefficientMem.openCoefficientExtension V g.val : Germ (𝓝 x) ℂ) at he
  obtain ⟨W, hWeq, hW, hxW⟩ := mem_nhds_iff.mp (Germ.coe_eq.mp he)
  let T : Opens E := (U ⊓ V) ⊓ ⟨W, hW⟩
  have hxT : x ∈ T := ⟨⟨hxU, hxV⟩, hxW⟩
  have hTU : T ≤ U := fun _ h => h.1.1
  have hTV : T ≤ V := fun _ h => h.1.2
  apply (FunctionSheaf.holomorphicFunctionPresheaf E).germ_ext T hxT (homOfLE hTU) (homOfLE hTV)
  apply Subtype.ext
  funext y
  have hy := hWeq y.property.2
  change CoefficientMem.openCoefficientExtension U f.val (y : E) = CoefficientMem.openCoefficientExtension V g.val (y : E) at hy
  rw [CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hTU y.property⟩,
    CoefficientMem.openCoefficientExtension_apply V _ ⟨y, hTV y.property⟩] at hy
  exact hy

theorem holomorphicStalkToGerm_surjective [FiniteDimensional ℂ E] (x : E) :
    Function.Surjective (StalkMap.AnalyticLocal.holomorphicStalkToGerm E x) := by
  intro a
  obtain ⟨U, hx, f, hf⟩ := SectionGerms.AnalyticLocal.exists_holomorphicSectionGerm x a
  exact ⟨(FunctionSheaf.holomorphicFunctionPresheaf E).germ U x hx f,
    (StalkMap.AnalyticLocal.holomorphicStalkToGerm_germ_apply E x U hx f).trans hf⟩

def holomorphicFunctionStalkEquiv [FiniteDimensional ℂ E] (x : E) :
    (FunctionSheaf.holomorphicFunctionPresheaf E).stalk x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  RingEquiv.ofBijective (StalkMap.AnalyticLocal.holomorphicStalkToGerm E x)
    ⟨holomorphicStalkToGerm_injective E x, holomorphicStalkToGerm_surjective E x⟩

theorem holomorphicFunctionStalk_noetherian [FiniteDimensional ℂ E] (x : E) :
    IsNoetherianRing ((FunctionSheaf.holomorphicFunctionPresheaf E).stalk x) := by
  let : IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) := NoetherianHolomorphicGerms.AnalyticLocal.holomorphic_germ_noetherian x
  exact isNoetherianRing_of_ringEquiv _ (holomorphicFunctionStalkEquiv E x).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkGerms.AnalyticLocal
