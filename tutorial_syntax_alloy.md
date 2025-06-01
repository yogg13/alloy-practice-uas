# Tutorial Lengkap Alloy: Sistem Registrasi Mata Kuliah

Alloy adalah bahasa pemodelan formal yang berguna untuk menggambarkan struktur dan batasan sistem. Tutorial ini menggunakan studi kasus komprehensif sistem registrasi mata kuliah yang mencakup perhitungan IPK, manajemen ruangan, daftar tunggu, dan berbagai fitur lanjutan.

## Daftar Isi

1. [Statement-Statement Dasar Alloy](#statement-statement-dasar-alloy)
2. [Konsep Inti Alloy](#konsep-inti-alloy)
3. [Model Lengkap: Sistem Registrasi Mata Kuliah](#model-lengkap-sistem-registrasi-mata-kuliah)
4. [Fitur Lanjutan](#fitur-lanjutan)
5. [Testing dan Validasi](#testing-dan-validasi)
6. [Panduan Eksekusi](#panduan-eksekusi)

## Penjelasan Statement-Statement Dasar Alloy

Sebelum kita mulai dengan konsep inti, mari pahami terlebih dahulu statement-statement dasar dalam Alloy:

### Kuantifikasi

- **`all`**: "untuk semua" atau "untuk setiap"
  - Contoh: `all m: Mahasiswa | #(m.mengambil) <= 5`
  - Artinya: Untuk setiap mahasiswa, jumlah mata kuliah yang diambil tidak boleh lebih dari 5.

- **`some`**: "setidaknya ada satu" atau "ada beberapa"
  - Contoh: `some m: Mahasiswa | m.mengambil = mk`
  - Artinya: Ada setidaknya satu mahasiswa yang mengambil mata kuliah mk.

- **`no`**: "tidak ada"
  - Contoh: `no m: Mahasiswa | m.mengambil = mk`
  - Artinya: Tidak ada mahasiswa yang mengambil mata kuliah mk.

- **`lone`**: "paling banyak satu"
  - Contoh: `lone m: Mahasiswa | m.mengambil = mk`
  - Artinya: Paling banyak ada satu mahasiswa yang mengambil mata kuliah mk.

- **`one`**: "tepat satu"
  - Contoh: `one m: Mahasiswa | m.mengambil = mk`
  - Artinya: Tepat ada satu mahasiswa yang mengambil mata kuliah mk.

### Variabel dan Deklarasi

- **`m:`, `mk:`, `pr:`, `d:`**: Deklarasi variabel dengan tipe tertentu
  - Contoh: `m: Mahasiswa` berarti m adalah variabel dengan tipe Mahasiswa
  - Artinya: Seperti mengatakan "misalkan m adalah seorang mahasiswa" atau "untuk setiap objek m yang merupakan Mahasiswa".

### Operator Dasar

- **`|` (pipe)**: Pemisah antara deklarasi variabel dan formula
  - Contoh: `all m: Mahasiswa | #(m.mengambil) <= 5`
  - Artinya: Pemisah yang berarti "sedemikian sehingga" atau "dengan syarat".

- **`#(...)` atau `#{...}`**: Menghitung jumlah elemen dalam set
  - Contoh: `#(m.mengambil)` menghitung jumlah mata kuliah yang diambil mahasiswa m
  - Contoh Kurung Kurawal: `#{m: Mahasiswa | mk in m.mengambil}` menghitung jumlah mahasiswa yang mengambil mata kuliah mk
  - Artinya: Operator untuk menghitung "berapa banyak".

- **`in`**: Relasi keanggotaan dalam set
  - Contoh: `mk in m.mengambil`
  - Artinya: Mata kuliah mk termasuk dalam set mata kuliah yang diambil oleh mahasiswa m.

- **`^` (transitive closure)**: Closure transitif dari relasi
  - Contoh: `mk.^prasyarat`
  - Artinya: Semua mata kuliah yang menjadi prasyarat dari mk, secara langsung maupun tidak langsung. 
  - Penjelasan Detail: Jika A adalah prasyarat B, dan B adalah prasyarat C, maka A dan B adalah anggota dari C.^prasyarat. Operator ini mencari semua elemen yang terhubung secara tidak langsung melalui sebuah relasi, seperti mencari "teman dari teman" atau "prasyarat dari prasyarat".

- **`*` (reflexive transitive closure)**: Closure transitif refleksif dari relasi
  - Contoh: `mk.*prasyarat`
  - Artinya: Seperti `^` tetapi termasuk juga dirinya sendiri.
  - Penjelasan Detail: Hampir sama dengan operator ^, tetapi juga menyertakan elemen awal itu sendiri. Ini seperti "saya, teman saya, dan teman dari teman saya".

### Operator Relasional Lainnya

- **`+` (union)**: Gabungan dua set
  - Contoh: `mahasiswaReguler + mahasiswaTransfer`
  - Artinya: Set yang berisi semua mahasiswa reguler dan semua mahasiswa transfer.

- **`&` (intersection)**: Irisan dua set
  - Contoh: `d.mengajar & m.mengambil`
  - Artinya: Set mata kuliah yang diajar oleh dosen d dan diambil oleh mahasiswa m.

- **`-` (difference)**: Selisih dua set
  - Contoh: `MataKuliah - m.mengambil`
  - Artinya: Set mata kuliah yang tidak diambil oleh mahasiswa m.

- **`.` (dot join)**: Menghubungkan relasi
  - Contoh: `m.mengambil`
  - Artinya: Set mata kuliah yang diambil oleh mahasiswa m.

- **`->` (product)**: Produk kartesian
  - Contoh: `Mahasiswa -> MataKuliah`
  - Artinya: Set semua pasangan mahasiswa-mata kuliah yang mungkin.

- **`=` (equal)**: Kesamaan
  - Contoh: `m.mengambil = mk`
  - Artinya: Set mata kuliah yang diambil mahasiswa m sama dengan mk.

- **`not` (negation)**: Negasi
  - Contoh: `mk not in m.mengambil`
  - Artinya: Mata kuliah mk tidak termasuk dalam set mata kuliah yang diambil oleh mahasiswa m.

- **`<=` (subset or less than or equal)**: Subset atau kurang dari sama dengan
  - Contoh: `#(m.mengambil) <= 5`
  - Artinya: Jumlah mata kuliah yang diambil oleh mahasiswa m tidak lebih dari 5.

## 1. Deklarasi Signature dan Field

**Signature (sig)** adalah cara untuk mendefinisikan tipe atau set objek dalam model Alloy. **Field** mendefinisikan relasi antara signature.

### Sintaks Dasar:

```alloy
sig NamaSig {
    namaField: [multiplisitas] TipeTujuan
}
```

### Contoh:

```alloy
// Signature sederhana tanpa field
sig Mahasiswa {}

// Signature dengan field
sig MataKuliah {
    prasyarat: set MataKuliah,
    kapasitas: one Int
}

// Signature dengan beberapa field
sig Dosen {
    mengajar: some MataKuliah,
    departemen: one Departemen
}

// Signature dengan extend (inheritance)
abstract sig Orang {}
sig Mahasiswa extends Orang {
    mengambil: set MataKuliah
}
sig Dosen extends Orang {
    mengajar: set MataKuliah
}
```

### Jenis Multiplisitas:
- `one`: tepat satu
- `lone`: nol atau satu
- `some`: satu atau lebih
- `set`: nol atau lebih (default)

## 2. Ekspresi Relasional

Ekspresi relasional digunakan untuk memanipulasi relasi dalam model.

### Operator Dasar:
- **Dot Join** (`.`): menghubungkan relasi
- **Product** (`->`): produk kartesian
- **Union** (`+`): gabungan relasi
- **Difference** (`-`): selisih relasi
- **Intersection** (`&`): irisan relasi

### Contoh:

```alloy
// m.mengambil adalah set mata kuliah yang diambil oleh mahasiswa m
all m: Mahasiswa | #(m.mengambil) <= 5

// d.mengajar adalah set mata kuliah yang diajar oleh dosen d
all d: Dosen | some d.mengajar

// Semua mahasiswa yang mengambil mata kuliah yang diajar oleh dosen tertentu
all d: Dosen | some m: Mahasiswa | some (m.mengambil & d.mengajar)
```

## 3. Predikat dan Fungsi

**Predikat (pred)** mendefinisikan batasan yang bisa benar atau salah. **Fungsi (fun)** mengembalikan nilai.

### Sintaks Predikat:

```alloy
pred namaPred[parameter: Tipe] {
    // batasan
}
```

### Sintaks Fungsi:

```alloy
fun namaFungsi[parameter: Tipe]: HasilTipe {
    // ekspresi yang mengembalikan nilai
}
```

### Contoh:

```alloy
// Predikat untuk mahasiswa yang mengambil mata kuliah dengan prasyarat terpenuhi
pred prasyaratTerpenuhi[m: Mahasiswa] {
    all mk: m.mengambil | all pr: mk.prasyarat | pr in m.mengambil
}

// Fungsi untuk mendapatkan semua dosen yang mengajar mata kuliah yang diambil oleh mahasiswa
fun dosenPengajar[m: Mahasiswa]: set Dosen {
    {d: Dosen | some (d.mengajar & m.mengambil)}
}
```

## 4. Constraints (Fakta, Asertif)

**Fakta (fact)** adalah batasan yang selalu benar dalam model. **Asertif (assert)** adalah properti yang ingin diuji.

### Sintaks Fakta:

```alloy
fact namaFakta {
    // batasan yang selalu benar
}
```

### Sintaks Asertif:

```alloy
assert namaAsertif {
    // properti yang ingin diuji
}
```

### Contoh:

```alloy
// Fakta: setiap mata kuliah memiliki kapasitas maksimal
fact KapasitasMaksimal {
    all mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} <= mk.kapasitas
}

// Asertif: tidak ada mahasiswa yang mengambil lebih dari 5 mata kuliah
assert MaksimalMataKuliah {
    all m: Mahasiswa | #(m.mengambil) <= 5
}
```

## 5. Command (run, check)

**Run** digunakan untuk mencari contoh model yang memenuhi batasan. **Check** digunakan untuk mencari counterexample yang melanggar asertif.

### Sintaks:

```alloy
run namaPredOrExp [scope]
check namaAsertif [scope]
```

### Contoh:

```alloy
// Mencari contoh model dengan prasyarat terpenuhi
run prasyaratTerpenuhi for 4

// Memeriksa apakah asertif MaksimalMataKuliah benar
check MaksimalMataKuliah for 5
```

## Studi Kasus: Sistem Registrasi Mata Kuliah

Mari kita buat model lengkap untuk sistem registrasi mata kuliah sederhana:

```alloy
module registrasiMataKuliah

// Definisi signature
sig Mahasiswa {
    mengambil: set MataKuliah
}

sig MataKuliah {
    prasyarat: set MataKuliah,
    kapasitas: one Int,
    diajarOleh: one Dosen
}

sig Dosen {
    departemen: one Departemen
}

sig Departemen {}

// Fakta-fakta dasar
fact KapasitasMaksimal {
    // Jumlah mahasiswa yang mengambil mata kuliah tidak melebihi kapasitas
    all mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} <= mk.kapasitas
}

fact PrasyaratValid {
    // Mata kuliah tidak bisa menjadi prasyarat untuk dirinya sendiri (langsung atau tidak langsung)
    all mk: MataKuliah | mk not in mk.^prasyarat
}

// Predikat
pred registrasiValid[m: Mahasiswa] {
    // Mahasiswa tidak mengambil lebih dari 5 mata kuliah
    #(m.mengambil) <= 5
    
    // Semua prasyarat terpenuhi
    all mk: m.mengambil | all pr: mk.prasyarat | pr in m.mengambil
}

// Fungsi
fun mataKuliahPerDepartemen[d: Departemen]: set MataKuliah {
    {mk: MataKuliah | mk.diajarOleh.departemen = d}
}

// Asertif
assert TidakAdaBentrok {
    // Tidak ada mahasiswa yang mengambil lebih dari 5 mata kuliah
    all m: Mahasiswa | #(m.mengambil) <= 5
}

// Command
run registrasiValid for 4 but 5 Int
check TidakAdaBentrok for 5
```

## Penjelasan Langkah demi Langkah

### Langkah 1: Mendefinisikan Signature dan Field
```alloy
sig Mahasiswa {
    mengambil: set MataKuliah
}

sig MataKuliah {
    prasyarat: set MataKuliah,
    kapasitas: one Int,
    diajarOleh: one Dosen
}

sig Dosen {
    departemen: one Departemen
}

sig Departemen {}
```

- `Mahasiswa` memiliki relasi `mengambil` yang menunjukkan set mata kuliah yang diambil
- `MataKuliah` memiliki relasi `prasyarat` (mata kuliah yang harus diambil sebelumnya), `kapasitas` (jumlah mahasiswa maksimal), dan `diajarOleh` (dosen pengajar)
- `Dosen` memiliki relasi `departemen` yang menunjukkan departemen tempat dosen bekerja
- `Departemen` adalah signature tanpa field

### Langkah 2: Mendefinisikan Fakta
```alloy
fact KapasitasMaksimal {
    all mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} <= mk.kapasitas
}

fact PrasyaratValid {
    all mk: MataKuliah | mk not in mk.^prasyarat
}
```

- Fakta `KapasitasMaksimal` memastikan jumlah mahasiswa yang mengambil mata kuliah tidak melebihi kapasitas mata kuliah
- Fakta `PrasyaratValid` memastikan tidak ada mata kuliah yang menjadi prasyarat untuk dirinya sendiri (secara langsung atau tidak langsung). Operator `^` adalah operator transitive closure

### Langkah 3: Mendefinisikan Predikat
```alloy
pred registrasiValid[m: Mahasiswa] {
    #(m.mengambil) <= 5
    all mk: m.mengambil | all pr: mk.prasyarat | pr in m.mengambil
}
```

- Predikat `registrasiValid` memeriksa apakah registrasi mahasiswa valid:
  - Mahasiswa tidak mengambil lebih dari 5 mata kuliah
  - Semua prasyarat untuk mata kuliah yang diambil juga diambil oleh mahasiswa

### Langkah 4: Mendefinisikan Fungsi
```alloy
fun mataKuliahPerDepartemen[d: Departemen]: set MataKuliah {
    {mk: MataKuliah | mk.diajarOleh.departemen = d}
}
```

- Fungsi `mataKuliahPerDepartemen` mengembalikan semua mata kuliah yang diajar oleh dosen dari departemen tertentu

### Langkah 5: Mendefinisikan Asertif
```alloy
assert TidakAdaBentrok {
    all m: Mahasiswa | #(m.mengambil) <= 5
}
```

- Asertif `TidakAdaBentrok` memeriksa apakah benar bahwa tidak ada mahasiswa yang mengambil lebih dari 5 mata kuliah

### Langkah 6: Mendefinisikan Command
```alloy
run registrasiValid for 4 but 5 Int
check TidakAdaBentrok for 5
```

- Command `run` mencari contoh instansi model yang memenuhi predikat `registrasiValid` dengan maksimal 4 objek untuk setiap signature, tetapi memungkinkan bilangan bulat hingga 5
- Command `check` mencari counterexample yang melanggar asertif `TidakAdaBentrok` dengan batasan maksimal 5 objek untuk setiap signature

## Pengujian dan Analisis

Setelah membuat model, Anda dapat menjalankan Alloy Analyzer untuk:

1. **Visualisasi Model**: Dengan menjalankan perintah `run`, Alloy Analyzer akan mencari instansi model yang memenuhi semua batasan dan menampilkannya secara visual.

2. **Validasi Properti**: Dengan menjalankan perintah `check`, Alloy Analyzer akan mencari counterexample yang melanggar asertif yang diberikan.

3. **Eksplorasi Alternatif**: Anda dapat menelusuri berbagai instansi model yang memenuhi batasan untuk memahami berbagai skenario yang mungkin.

4. **Perbaikan Model**: Berdasarkan hasil analisis, Anda dapat memperbaiki model untuk lebih akurat menggambarkan domain masalah.

Dengan menggunakan Alloy untuk pemodelan formal, Anda dapat menemukan inkonsistensi dan masalah dalam desain sistem sebelum implementasi, yang dapat menghemat waktu dan sumber daya dalam pengembangan perangkat lunak.
