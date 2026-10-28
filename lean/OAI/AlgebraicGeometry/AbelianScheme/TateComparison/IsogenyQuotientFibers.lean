import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricFlags
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELKernelTransport

/-! # Isogeny Quotient Fibers -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The one-step IsogenyQuotient input gives actual marked polarized isogenies on
geometric fibers and a bijection between branches and their chosen kernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  {k : Type} [Field k] {b : Spec (.of k) ⟶ Spec (.of K)}

def Data.SphericalPELAlbaneseData.sourceFamilyFiberIso (t : Local.IntegralType s) (x : D.GeometricPoint b)
    (c : Over.mk b ⟶ (D.correspondence t).cover)
    (hc : c ≫ (D.correspondence t).source = x) :
    PELModuli.PELFamilyIso (D.fiberFamily b x) ((D.sourceFamily t).pullback c.left) :=
  D.family.pullbackFactor c.left (D.correspondence t).source.left x.left
    (congrArg (fun z => z.left) hc)

def Data.SphericalPELAlbaneseData.targetFamilyFiberIso (t : Local.IntegralType s) (y : D.GeometricPoint b)
    (c : Over.mk b ⟶ (D.correspondence t).cover)
    (hc : c ≫ (D.correspondence t).target = y) :
    PELModuli.PELFamilyIso (D.fiberFamily b y) ((D.targetFamily t).pullback c.left) :=
  D.family.pullbackFactor c.left (D.correspondence t).target.left y.left
    (congrArg (fun z => z.left) hc)

/-- This is the actual pullback of the universal IsogenyQuotient isogeny, transported
to the named geometric source and target families. -/
def Data.SphericalPELAlbaneseData.c46FiberIsogeny (h : D.RealizesIsogenyQuotient) (t : Local.IntegralType s)
    (x y : D.GeometricPoint b) (c : Over.mk b ⟶ (D.correspondence t).cover)
    (hs : c ≫ (D.correspondence t).source = x)
    (ht : c ≫ (D.correspondence t).target = y) :
    PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ t.multiplierNat) :=
  ((D.c46Isogeny h t).pullback c.left).transport
    (D.sourceFamilyFiberIso t x c hs) (D.targetFamilyFiberIso t y c ht).symm

theorem Data.SphericalPELAlbaneseData.chosenKernelAtLift_as_comap (h : D.RealizesIsogenyQuotient) (t : Local.IntegralType s)
    (x : D.GeometricPoint b) (c : Over.mk b ⟶ (D.correspondence t).cover)
    (hc : c ≫ (D.correspondence t).source = x) (v : Fin s) :
    D.chosenKernelAtLift t (D.c46Isogeny h t) x c hc v =
      ((D.universalChosenKernel t (D.c46Isogeny h t) v).pullback c.left).comapHom
        (D.sourceFamilyFiberIso t x c hc).abelian.hom := by
  have he := D.family.pullbackFactor_abelian c.left (D.correspondence t).source.left x.left
    (congrArg (fun z => z.left) hc)
  unfold Data.SphericalPELAlbaneseData.chosenKernelAtLift Data.SphericalPELAlbaneseData.sourceFamilyFiberIso
  apply Subgroups.PointSubgroup.comapHom_congr
  exact (congrArg Iso.hom he).symm

theorem Data.SphericalPELAlbaneseData.c46FiberIsogeny_kernel (h : D.RealizesIsogenyQuotient) (t : Local.IntegralType s)
    (x y : D.GeometricPoint b) (c : Over.mk b ⟶ (D.correspondence t).cover)
    (hs : c ≫ (D.correspondence t).source = x)
    (ht : c ≫ (D.correspondence t).target = y) (v : Fin s) :
    (Subgroups.PointSubgroup.kernel (D.c46FiberIsogeny h t x y c hs ht).isogeny.hom).inf
      (Subgroups.splitBlock (D.fiberFamily b x) (D.localCharacter (v, false)) t.multiplierNat) =
      D.chosenKernelAtLift t (D.c46Isogeny h t) x c hs v := by
  rw [Data.SphericalPELAlbaneseData.c46FiberIsogeny, PELIsogenies.PELIsogeny.splitKernel_transport, Data.SphericalPELAlbaneseData.chosenKernelAtLift_as_comap]
  congr 1
  rw [Data.SphericalPELAlbaneseData.universalChosenKernel, Subgroups.PointSubgroup.pullback_inf, Subgroups.PointSubgroup.pullback_kernel,
    SplitSubgroups.splitBlock_pullback]
  rfl

/-- The branch's kernels are actual independent finite-etale choices of
the stated geometric elementary type. These facts follow by transport. -/
def Data.SphericalPELAlbaneseData.c46FiberKernelChoice (h : D.RealizesIsogenyQuotient) (t : Local.IntegralType s)
    (x : D.GeometricPoint b) (c : (D.correspondence t).Fiber x) : D.chosenKernels t x := by
  refine ⟨D.chosenKernelAtLift t (D.c46Isogeny h t) x c.val c.property, ?_⟩
  intro v
  have hf := (h t).choose_spec.1 v
  change (D.universalChosenKernel t (D.c46Isogeny h t) v).HasFiniteEtaleModel ∧
    (D.universalChosenKernel t (D.c46Isogeny h t) v).HasGeometricType q (t.exponentNat v) at hf
  rw [D.chosenKernelAtLift_as_comap h t x c.val c.property v]
  refine ⟨Subgroups.PointSubgroup.hasFiniteEtaleModel_comapIso (A := (D.fiberFamily b x).abelian) _
      (Subgroups.PointSubgroup.hasFiniteEtaleModel_pullback _ hf.1 c.val.left) _, ?_,
    Subgroups.PointSubgroup.hasGeometricType_comapIso (A := (D.fiberFamily b x).abelian) _
      (Subgroups.PointSubgroup.hasGeometricType_pullback _ hf.2 c.val.left) _⟩
  have hsplit :
      ((Subgroups.splitBlock (D.sourceFamily t) (D.localCharacter (v, false)) t.multiplierNat).pullback c.val.left).comapHom
        (D.sourceFamilyFiberIso t x c.val c.property).abelian.hom =
          Subgroups.splitBlock (D.fiberFamily b x) (D.localCharacter (v, false)) t.multiplierNat := by
    rw [SplitSubgroups.splitBlock_pullback]
    exact SplitSubgroups.splitBlock_comapIso (D.sourceFamilyFiberIso t x c.val c.property) _ _
  intro T z hz
  have hz' : z ∈
      (((Subgroups.splitBlock (D.sourceFamily t) (D.localCharacter (v, false)) t.multiplierNat).pullback c.val.left).comapHom
        (D.sourceFamilyFiberIso t x c.val c.property).abelian.hom).atTest T := hz.2
  rw [hsplit] at hz'
  exact hz'

theorem Data.SphericalPELAlbaneseData.c46FiberKernelChoice_bijective (h : D.RealizesIsogenyQuotient) (t : Local.IntegralType s)
    (x : D.GeometricPoint b) : Function.Bijective (D.c46FiberKernelChoice h t x) := by
  have : IsReduced (Over.mk b).left := inferInstanceAs (IsReduced (Spec (.of k)))
  have hclass := (h t).choose_spec.2.1
  constructor
  · intro c d hcd
    obtain ⟨a, ha, huniq⟩ := hclass (Over.mk b) x (D.c46FiberKernelChoice h t x c)
    apply Subtype.ext
    apply (huniq c.val ⟨c.property, fun _ => rfl⟩).trans
    apply (huniq d.val ?_).symm
    refine ⟨d.property, ?_⟩
    intro v
    exact congrArg (fun F : D.chosenKernels t x => F.val v) hcd.symm
  · intro F
    obtain ⟨c, ⟨hc, hk⟩, _⟩ := hclass (Over.mk b) x F
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    funext v
    exact hk v

def Data.SphericalPELAlbaneseData.c46FiberKernelEquiv (h : D.RealizesIsogenyQuotient) (t : Local.IntegralType s) (x : D.GeometricPoint b) :
    (D.correspondence t).Fiber x ≃ D.chosenKernels t x :=
  Equiv.ofBijective (D.c46FiberKernelChoice h t x) (D.c46FiberKernelChoice_bijective h t x)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
