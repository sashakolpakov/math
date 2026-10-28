import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CommonPrincipalWedges
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.HeckeCycles
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Albanese

/-! # CM Wedge Albanese -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMWedgeAlbanese.CM

noncomputable section

/-! Native Albanese extraction from the constructed CM wedge product.
The two holomorphic factors use id and the conjugated two use c. -/

open _root_.CategoryTheory

theorem cm_wedge_product_algebraic_maps
    (hDegreeTwo : Albanese.CM.ConditionalWeightOneInput) (hHolomorphicAlgebraicity : DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput) (hConstruction : DegreeTwo.Transport.Constructions.ConstructionInput)
    (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)))
    (S : Cm.ProjectiveSurface) (hS : CommonPrincipalWedges.CM.HasCMWedgeProduct K (v := v) S) :
    ∃ f : (i : Fin 4) → S.variety.toOver ⟶ (R i).abelianVariety.toOver,
      S.evaluate (Cm.fourClass K v R S.variety f) ≠ 0 := by
  obtain ⟨ξ, ζ, hξ, hζ, hn⟩ := hS
  let H := Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 S.variety
  let Θ : Fin 4 → Submodule ℂ (S.variety.complexCohomology 1) :=
    fun i => Cm.cmLineSpan K S.variety H (v i) (Extraction.CM.slotLabel K i)
  exact HeckeCycles.CM.algebraic_maps_of_wedge_data_native K v R
    (Albanese.CM.p23_weight_one_of_conditional hDegreeTwo hHolomorphicAlgebraicity hConstruction HeckeCycles.CM.nativeHodgeComparisonInput) hConstruction
    S H (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1_isCanonical S.variety) Θ (fun _ => le_rfl)
    ξ ζ hξ hζ hn

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMWedgeAlbanese.CM
