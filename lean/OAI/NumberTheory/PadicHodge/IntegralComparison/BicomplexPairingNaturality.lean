import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexPairing

/-! # Bicomplex Pairing Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexPairingNaturality

noncomputable section

/-! Natural bidegree pairings induce natural pairings on the original
total complexes. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R]
  {K L M K' L' M' : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)}
  [K.HasTotal (.up ℕ)] [L.HasTotal (.up ℕ)] [M.HasTotal (.up ℕ)]
  [K'.HasTotal (.up ℕ)] [L'.HasTotal (.up ℕ)] [M'.HasTotal (.up ℕ)]
  (μ : ∀ p a q b, (K.X p).X a →ₗ[R] (L.X q).X b →ₗ[R] (M.X (p + q)).X (a + b))
  (ν : ∀ p a q b, (K'.X p).X a →ₗ[R] (L'.X q).X b →ₗ[R] (M'.X (p + q)).X (a + b))
  (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M')
  (hμ : ∀ p a q b (x : (K.X p).X a) (y : (L.X q).X b),
    (h.f (p + q)).f (a + b) (μ p a q b x y) =
      ν p a q b ((f.f p).f a x) ((g.f q).f b y))

include hμ in
theorem totalPairing_natural (n m : ℕ) (x : (K.total (.up ℕ)).X n) (y : (L.total (.up ℕ)).X m) :
    (HomologicalComplex₂.total.map h (.up ℕ)).f (n + m) (BicomplexPairing.totalPairing K L M μ n m x y) =
      BicomplexPairing.totalPairing K' L' M' ν n m ((HomologicalComplex₂.total.map f (.up ℕ)).f n x)
        ((HomologicalComplex₂.total.map g (.up ℕ)).f m y) := by
  let A := (BicomplexPairing.totalPairing K L M μ n m).compr₂
    ((HomologicalComplex₂.total.map h (.up ℕ)).f (n + m)).hom
  let B := (BicomplexPairing.totalPairing K' L' M' ν n m).compl₁₂
    ((HomologicalComplex₂.total.map f (.up ℕ)).f n).hom
    ((HomologicalComplex₂.total.map g (.up ℕ)).f m).hom
  have he : A = B := by
    apply BicomplexPairing.bilinear_ext K L n m
    intro p a q b hpa hqb u v
    have hf := ConcreteCategory.congr_hom (K.ιTotal_map K' f (.up ℕ) p a n hpa) u
    have hg := ConcreteCategory.congr_hom (L.ιTotal_map L' g (.up ℕ) q b m hqb) v
    change (HomologicalComplex₂.total.map f (.up ℕ)).f n (K.ιTotal (.up ℕ) p a n hpa u) =
      K'.ιTotal (.up ℕ) p a n hpa ((f.f p).f a u) at hf
    change (HomologicalComplex₂.total.map g (.up ℕ)).f m (L.ιTotal (.up ℕ) q b m hqb v) =
      L'.ιTotal (.up ℕ) q b m hqb ((g.f q).f b v) at hg
    have hh := ConcreteCategory.congr_hom
      (M.ιTotal_map M' h (.up ℕ) (p + q) (a + b) (n + m) (by
        change (p + q) + (a + b) = n + m
        omega)) (μ p a q b u v)
    change (HomologicalComplex₂.total.map h (.up ℕ)).f (n + m)
        (BicomplexPairing.totalPairing K L M μ n m (K.ιTotal (.up ℕ) p a n hpa u) (L.ιTotal (.up ℕ) q b m hqb v)) = _
    exact (congrArg ((HomologicalComplex₂.total.map h (.up ℕ)).f (n + m))
      (BicomplexPairing.totalPairing_ι K L M μ n m p a q b hpa hqb u v)).trans
        (hh.trans ((congrArg (M'.ιTotal (.up ℕ) (p + q) (a + b) (n + m) (by
          change (p + q) + (a + b) = n + m
          omega)) (hμ p a q b u v)).trans
          ((BicomplexPairing.totalPairing_ι K' L' M' ν n m p a q b hpa hqb ((f.f p).f a u) ((g.f q).f b v)).symm.trans
            (congrArg₂ (fun s t => BicomplexPairing.totalPairing K' L' M' ν n m s t) hf.symm hg.symm))))
  exact DFunLike.congr_fun (DFunLike.congr_fun he x) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexPairingNaturality
