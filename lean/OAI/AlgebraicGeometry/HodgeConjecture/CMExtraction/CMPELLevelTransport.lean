import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FinitePELHomeomorph
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicContainment
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenLevelTransport

/-! # CMPEL Level Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELLevelTransport.Approximation

noncomputable section

/-! Transport an actual source open level to the specified PEL finite
group. Its principal containment depth is chosen before any finite prime. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicContainment OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (hb : IsCMField.complexConj E P.b = P.b) (hb0 : P.b ≠ 0)
  (L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hb hb0)))

def cmPELTransportLevel : OpenSubgroup P.FiniteSpecialUnitary :=
  OpenLevelTransport.Approximation.transportOpenLevel (CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0) L

theorem cmPELTransportLevel_mem
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hb hb0)) :
    CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0 g ∈ cmPELTransportLevel E δ hδ hδ0 P hb hb0 L ↔
      g ∈ L :=
  OpenLevelTransport.Approximation.transportOpenLevel_mem (CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0) L g

theorem cm_source_level_principal_depth
    (hfg : P.lattice.FG)
    (hspan : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ∣ N →
      ∀ g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hb hb0),
        CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0 g ∈ P.adelicPrincipalLevel N → g ∈ L :=
  OpenLevelTransport.Approximation.transportOpenLevel_principal_depth (CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0) L P.adelicPrincipalLevel
    (AbelianModuli.ReferenceFamily.AdelicContainment.exists_adelic_principal_containment_depth P hfg hspan (cmPELTransportLevel E δ hδ hδ0 P hb hb0 L))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELLevelTransport.Approximation
