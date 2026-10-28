import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.LineBundleSectionCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulAcyclic

/-! # Line Bundle Koszul -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Finite global generation constructs a bounded exact section Koszul complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.exists_acyclic_koszul {X : Scheme.{u}}
    (L : Line.Bundles.LineBundle X) (hL : HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators L.sheaf) :
    ∃ ss : List (Line.Bundles.structureModule X ⟶ L.sheaf), ∀ M : X.Modules,
      (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).Acyclic ∧
      ∀ i : ℤ, i < -(ss.length : ℤ) ∨ 0 < i →
        IsZero ((LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X i) := by
  classical
  obtain ⟨ι, hι, s, hs⟩ := HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.lineBundle_section_cover L hL
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let ss := (Finset.univ : Finset ι).toList.map s
  refine ⟨ss, ?_⟩
  intro M
  refine ⟨?_, LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X L M ss⟩
  apply LineBundle.SectionKoszulAcyclic.lineBundleSectionKoszulComplex_acyclic L M ss
    (fun i => Ample.LineBundles.sectionNonvanishing (s i)) hs
  intro i
  refine ⟨s i, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩
  · exact (Section.Nonvanishing.isIso_pullbackSection_iff (Ample.LineBundles.sectionNonvanishing (s i)).ι (s i)).mp inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
