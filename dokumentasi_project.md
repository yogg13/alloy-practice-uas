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

### Fakta-Fakta Utama (Constraints)

#### 1. Kapasitas dan Registrasi

```alloy
fact KapasitasMaksimal {
    // Jumlah mahasiswa yang mengambil mata kuliah tidak melebihi kapasitas
    all mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} <= mk.kapasitas
}
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Definisi Constraint Global `fact KapasitasMaksimal`**

- **Tujuan:** Menciptakan aturan yang berlaku untuk seluruh model tanpa pengecualian
- **Alasan Penggunaan `fact`:** Facts selalu diberlakukan dalam semua instance model, tidak seperti predicates yang bisa dipilih untuk dijalankan
- **Dampak:** Memastikan semua solusi model mematuhi batasan kapasitas kelas

**Step 2: Kuantifikasi Universal `all mk: MataKuliah`**

- **Tujuan:** Menerapkan aturan pada setiap mata kuliah dalam sistem
- **Alasan Penggunaan `all`:** Aturan kapasitas harus berlaku untuk semua mata kuliah tanpa kecuali
- **Mekanisme Kerja:** Alloy akan memeriksa setiap instance MataKuliah satu per satu

**Step 3: Perhitungan Set `#{m: Mahasiswa | mk in m.mengambil}`**

- **Tujuan:** Menghitung jumlah mahasiswa yang mengambil mata kuliah tertentu
- **Alasan Teknis:** Operator `#` menghitung kardinalitas set, dengan set comprehension di dalamnya
- **Logika:** `mk in m.mengambil` memilih mahasiswa yang mengambil mata kuliah mk
- **Hasil:** Jumlah total mahasiswa yang terdaftar di mata kuliah mk

**Step 4: Pembatasan `<= mk.kapasitas`**

- **Tujuan:** Memastikan jumlah mahasiswa tidak melebihi kapasitas yang ditetapkan
- **Alasan Bisnis:** Ruangan fisik dan kualitas pengajaran memiliki batasan jumlah peserta
- **Konsekuensi:** Alloy akan menolak semua model yang melanggar batasan ini
- **Manfaat Praktis:** Mencegah oversubscription dan menjaga kualitas pembelajaran

#### 2. Validasi Prasyarat

```alloy
fact PrasyaratValid {
    // Mata kuliah tidak bisa menjadi prasyarat untuk dirinya sendiri
    all mk: MataKuliah | mk not in mk.^prasyarat
}
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Definisi Constraint Antisiklus `fact PrasyaratValid`**

- **Tujuan:** Mencegah siklus prasyarat yang tidak logis dalam kurikulum
- **Alasan Kebutuhan:** Siklus prasyarat membuat mata kuliah tidak mungkin diambil (deadlock)
- **Dampak Akademik:** Memastikan jalur studi mahasiswa selalu memiliki titik awal yang jelas

**Step 2: Kuantifikasi Universal `all mk: MataKuliah`**

- **Tujuan:** Menerapkan aturan anti-siklus pada setiap mata kuliah
- **Alasan Penggunaan `all`:** Tidak boleh ada pengecualian untuk aturan ini
- **Cakupan:** Memeriksa setiap mata kuliah dalam sistem satu per satu

**Step 3: Operator Transitive Closure `mk.^prasyarat`**

- **Tujuan:** Memeriksa seluruh rantai prasyarat secara rekursif
- **Alasan Penggunaan `^`:** Kita perlu memeriksa prasyarat langsung dan tidak langsung
- **Mekanisme Kerja:** Mulai dari mk, ikuti relasi prasyarat berulang kali
- **Contoh:** Jika A prasyarat B, dan B prasyarat C, maka A dan B adalah anggota C.^prasyarat

**Step 4: Negasi Keanggotaan `mk not in`**

- **Tujuan:** Mencegah mata kuliah mereferensi dirinya sendiri dalam rantai prasyarat
- **Alasan Logis:** Mata kuliah tidak dapat membutuhkan dirinya sendiri sebagai prasyarat
- **Implementasi Teknis:** Memastikan mk tidak muncul dalam set mk.^prasyarat
- **Konsekuensi:** Menghilangkan siklus seperti A → B → C → A yang mustahil dipenuhi

#### 3. Manajemen Jadwal

```alloy
fact TidakAdaBentrokJadwal {
    // Mahasiswa tidak boleh mengambil mata kuliah dengan jadwal bertabrakan
    all m: Mahasiswa | all disj mk1, mk2: m.mengambil |
        no (mk1.jadwal & mk2.jadwal)
}
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Definisi Constraint Jadwal `fact TidakAdaBentrokJadwal`**

- **Tujuan:** Mencegah mahasiswa terdaftar di kelas yang berjalan secara bersamaan
- **Alasan Praktis:** Mahasiswa tidak dapat berada di dua tempat pada waktu yang sama
- **Dampak Akademik:** Memastikan mahasiswa dapat menghadiri semua kelas yang diambil

**Step 2: Kuantifikasi Mahasiswa `all m: Mahasiswa`**

- **Tujuan:** Menerapkan aturan jadwal untuk setiap mahasiswa dalam sistem
- **Alasan Penggunaan `all`:** Aturan ini berlaku tanpa pengecualian untuk semua mahasiswa
- **Cakupan:** Memeriksa jadwal setiap mahasiswa satu per satu

**Step 3: Kuantifikasi Pasangan Mata Kuliah `all disj mk1, mk2: m.mengambil`**

- **Tujuan:** Memeriksa setiap pasangan berbeda mata kuliah yang diambil seorang mahasiswa
- **Alasan Penggunaan `disj`:** Memastikan kita hanya membandingkan dua mata kuliah berbeda
- **Mekanisme:** Untuk setiap mahasiswa m, periksa semua pasangan mata kuliah yang diambilnya

**Step 4: Pemeriksaan Irisan Jadwal `no (mk1.jadwal & mk2.jadwal)`**

- **Tujuan:** Memastikan tidak ada slot waktu yang sama antara dua mata kuliah
- **Alasan Penggunaan `&`:** Operator irisan menemukan slot waktu yang sama antara dua jadwal
- **Alasan Penggunaan `no`:** Menentukan bahwa irisan harus kosong (tidak ada overlap)
- **Konsekuensi:** Model ditolak jika ada mahasiswa yang terdaftar di dua mata kuliah dengan jadwal bertabrakan

#### 4. Manajemen Ruangan

```alloy
fact KetersediaanRuangan {
    // Kapasitas ruangan mencukupi
    all mk: MataKuliah |
        mk.ruangan.kapasitas >= #{m: Mahasiswa | mk in m.mengambil}

    // Fasilitas yang dibutuhkan tersedia
    all mk: MataKuliah | mk.butuhanFasilitas in mk.ruangan.fasilitas

    // Tidak ada bentrok penggunaan ruangan
    all r: Ruangan, t: SlotWaktu |
        lone mk: MataKuliah | mk.ruangan = r and t in mk.jadwal
}
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Constraint Kapasitas Ruangan**

- **Tujuan:** Memastikan ruangan cukup besar untuk menampung semua mahasiswa terdaftar
- **Alasan Praktis:** Keamanan dan kenyamanan fisik mengharuskan penghitungan kapasitas
- **Implementasi Teknis:** Membandingkan kapasitas ruangan dengan jumlah mahasiswa terdaftar
- **Mekanisme Kerja:** `mk.ruangan.kapasitas` mengakses nilai kapasitas ruangan melalui relasi berantai

**Step 2: Constraint Ketersediaan Fasilitas**

- **Tujuan:** Memastikan ruangan memiliki semua fasilitas yang dibutuhkan mata kuliah
- **Alasan Penggunaan `in`:** Operator subset memeriksa apakah semua fasilitas yang dibutuhkan tersedia
- **Contoh Praktis:** Mata kuliah lab komputer membutuhkan ruangan dengan komputer
- **Konsekuensi:** Mencegah penempatan mata kuliah di ruangan yang tidak memadai

**Step 3: Constraint Pencegahan Bentrok Ruangan**

- **Tujuan:** Memastikan sebuah ruangan hanya digunakan oleh satu mata kuliah pada waktu tertentu
- **Alasan Penggunaan `lone`:** Maksimal satu mata kuliah bisa menggunakan ruangan pada slot waktu tertentu
- **Logika Implementasi:** Untuk setiap kombinasi ruangan dan slot waktu, cari mata kuliah yang menggunakannya
- **Dampak Kebijakan:** Mencegah double-booking ruangan, memastikan ketersediaan fisik

#### 5. Sistem Daftar Tunggu

```alloy
fact AturanDaftarTunggu {
    // Mahasiswa di daftar tunggu tidak sedang mengambil mata kuliah tersebut
    all mk: MataKuliah | all m: elems[mk.daftarTunggu] |
        m not in {mhs: Mahasiswa | mk in mhs.mengambil}
}
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Definisi Constraint Daftar Tunggu**

- **Tujuan:** Memastikan konsistensi antara pendaftaran aktif dan daftar tunggu
- **Alasan Bisnis:** Mahasiswa tidak seharusnya berada di daftar aktif dan tunggu secara bersamaan
- **Dampak Administrasi:** Mencegah duplikasi dan memastikan integritas data sistem registrasi

**Step 2: Kuantifikasi Universal `all mk: MataKuliah`**

- **Tujuan:** Menerapkan aturan untuk setiap mata kuliah dalam sistem
- **Alasan Penggunaan `all`:** Konsistensi daftar tunggu harus dijamin untuk semua mata kuliah
- **Cakupan:** Memeriksa setiap mata kuliah satu per satu

**Step 3: Extraksi Elemen Daftar Tunggu `all m: elems[mk.daftarTunggu]`**

- **Tujuan:** Memeriksa setiap mahasiswa dalam daftar tunggu mata kuliah
- **Alasan Penggunaan `elems`:** Mengkonversi sequence (urutan) menjadi set anggota
- **Signifikansi:** Mempertahankan urutan dalam daftar tunggu penting untuk fairness (FIFO)
- **Mekanisme:** Untuk setiap mahasiswa dalam daftar tunggu, terapkan constraint berikutnya

**Step 4: Negasi Keanggotaan Aktif `m not in {...}`**

- **Tujuan:** Memastikan mahasiswa di daftar tunggu tidak terdaftar aktif di mata kuliah
- **Alasan Penggunaan Set Comprehension:** Mendefinisikan set mahasiswa yang mengambil mata kuliah mk
- **Logika Validasi:** Mahasiswa m tidak boleh berada dalam set mahasiswa yang mengambil mata kuliah
- **Konsekuensi Operasional:** Sistem dapat secara otomatis memindahkan mahasiswa dari daftar tunggu ke aktif saat ada slot kosong

#### 6. Beban Kerja Dosen

```alloy
fact BebanKerjaDosen {
    // Tidak ada dosen yang mengajar lebih dari 3 mata kuliah
    all d: Dosen | #{mk: MataKuliah | mk.diajarOleh = d} <= 3

    // Total SKS yang diajarkan tidak melebihi 12 SKS
    all d: Dosen | (sum mk: MataKuliah | mk.diajarOleh = d => mk.sks else 0) <= 12
}
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Definisi Constraint Jumlah Mata Kuliah**

- **Tujuan:** Membatasi jumlah mata kuliah yang diajar oleh seorang dosen
- **Alasan Kebijakan:** Menjaga kualitas pengajaran dan mencegah burnout dosen
- **Implementasi Teknis:** Menghitung jumlah mata kuliah yang diajarkan setiap dosen
- **Batas Spesifik:** Maksimal 3 mata kuliah per dosen per semester

**Step 2: Kuantifikasi Universal Dosen `all d: Dosen`**

- **Tujuan:** Menerapkan batasan untuk setiap dosen dalam sistem
- **Alasan Penggunaan `all`:** Kebijakan beban kerja berlaku tanpa pengecualian
- **Cakupan:** Memeriksa beban kerja setiap dosen secara individual

**Step 3: Penghitungan Mata Kuliah `#{mk: MataKuliah | mk.diajarOleh = d}`**

- **Tujuan:** Menghitung jumlah mata kuliah yang diajarkan seorang dosen
- **Mekanisme Set Comprehension:** Memfilter mata kuliah berdasarkan dosen pengajar
- **Logika Filter:** Memilih mata kuliah yang field diajarOleh-nya sama dengan dosen d
- **Pengukuran:** Operator # menghitung jumlah elemen set hasil filter

**Step 4: Constraint Total SKS**

- **Tujuan:** Membatasi total beban SKS yang diajarkan oleh seorang dosen
- **Alasan Penggunaan `sum`:** Menjumlahkan SKS dari semua mata kuliah yang diajarkan
- **Sintaks Conditional:** `mk.diajarOleh = d => mk.sks else 0` hanya menambahkan SKS jika dosen mengajar mata kuliah
- **Batas Spesifik:** Maksimal 12 SKS per dosen per semester
- **Dampak Kebijakan:** Memastikan beban kerja yang seimbang dan berkelanjutan

### Fitur Lanjutan

#### 1. Fungsi Perhitungan IPK

Fungsi ini menghitung IPK mahasiswa berdasarkan nilai dan SKS mata kuliah:

```alloy
fun hitungIPK[m: Mahasiswa]: Int {
    // Dapatkan mata kuliah yang memiliki nilai
    let mksWithGrades = {mk: m.mengambil | some m.nilai[mk]} |

    // Jika tidak ada mata kuliah dengan nilai, kembalikan 0
    #mksWithGrades = 0 => 0 else (
        // Hitung total SKS
        let totalSKS = sum mk: mksWithGrades | mk.sks |

        // Jika total SKS 0, kembalikan 0
        totalSKS = 0 => 0 else (
            // Hitung total poin berdasarkan nilai dan SKS
            let sksA = sum mk: {mk: mksWithGrades | m.nilai[mk] = A} | mk.sks,
                sksB = sum mk: {mk: mksWithGrades | m.nilai[mk] = B} | mk.sks,
                sksC = sum mk: {mk: mksWithGrades | m.nilai[mk] = C} | mk.sks,
                sksD = sum mk: {mk: mksWithGrades | m.nilai[mk] = D} | mk.sks,
                totalPoints = add[add[add[mul[sksA, 4], mul[sksB, 3]], mul[sksC, 2]], sksD] |

            // Hitung IPK dengan format integer (350 = 3.50)
            div[mul[totalPoints, 100], totalSKS]
        )
    )
}
```

**Penjelasan Algoritma IPK:**

1. Mengidentifikasi mata kuliah yang memiliki nilai
2. Menghitung total SKS dari mata kuliah tersebut
3. Menghitung total poin dengan bobot: A=4, B=3, C=2, D=1, E=0
4. Formula: IPK = (Total Poin × 100) ÷ Total SKS
5. Hasil dalam format integer (contoh: 350 untuk IPK 3.50)

#### 2. Sistem Prioritas Registrasi

```alloy
pred prioritasRegistrasi[m1, m2: Mahasiswa] {
    // Mahasiswa senior memiliki prioritas lebih tinggi
    m1.semester > m2.semester or
    // Jika semester sama, yang IPK lebih tinggi diprioritaskan
    (m1.semester = m2.semester and m1.ipk > m2.ipk)
}
```

#### 3. Validasi Registrasi

```alloy
pred registrasiValid[m: Mahasiswa] {
    // Mahasiswa tidak mengambil lebih dari 5 mata kuliah
    #(m.mengambil) <= 5

    // Semua prasyarat terpenuhi
    all mk: m.mengambil | all pr: mk.prasyarat | pr in m.mengambil

    // Maksimum SKS per semester adalah 24
    (sum mk: m.mengambil | mk.sks) <= 24
}
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Batas Jumlah Mata Kuliah `#(m.mengambil) <= 5`**

- **Tujuan:** Mencegah mahasiswa mengambil terlalu banyak mata kuliah dalam satu semester
- **Alasan Batasan:** Mata kuliah membutuhkan waktu dan energi; terlalu banyak mata kuliah dapat menurunkan kualitas pembelajaran
- **Implementasi Teknis:** Menggunakan operator `#` untuk menghitung jumlah mata kuliah dalam set `m.mengambil`
- **Dampak Bisnis:** Memastikan mahasiswa fokus pada beberapa mata kuliah dan mencapai hasil maksimal

**Step 2: Validasi Prasyarat `all mk: m.mengambil | all pr: mk.prasyarat | pr in m.mengambil`**

- **Tujuan:** Memastikan mahasiswa telah mengambil semua mata kuliah prasyarat
- **Alasan Pedagogis:** Materi kuliah sering bersifat sekuensial; konsep dasar diperlukan sebelum konsep lanjutan
- **Implementasi Teknis:** Nested quantifier (`all`) untuk memeriksa seluruh prasyarat (`pr`) dari setiap mata kuliah yang diambil (`mk`)
- **Logika Validasi:** `pr in m.mengambil` memeriksa apakah prasyarat terdapat dalam set mata kuliah yang diambil
- **Dampak Akademik:** Mencegah mahasiswa mengambil mata kuliah tanpa fondasi pengetahuan yang cukup

**Step 3: Batas SKS `(sum mk: m.mengambil | mk.sks) <= 24`**

- **Tujuan:** Membatasi beban studi mahasiswa dalam satu semester
- **Alasan Akademik:** Standar beban studi maksimal sesuai dengan regulasi pendidikan tinggi di Indonesia
- **Implementasi Teknis:** Operator `sum` untuk menghitung total SKS dari semua mata kuliah yang diambil
- **Mekanisme Kerja:** Untuk setiap mata kuliah dalam `m.mengambil`, jumlahkan nilai field `sks`
- **Dampak Administratif:** Memastikan kepatuhan terhadap aturan akademik dan mencegah overload mahasiswa

## Testing dan Validasi

### Assertion untuk Validasi Model

```alloy
// Validasi perhitungan IPK
assert IPKCalculationValid {
    all m: Mahasiswa | hitungIPK[m] >= 0 and hitungIPK[m] <= 400
}

// Validasi penegakan prasyarat
assert PrerequisitesEnforced {
    all m: Mahasiswa, mk: m.mengambil |
        all prereq: mk.prasyarat | prereq in m.mengambil
}

// Validasi tidak ada konflik ruangan
assert NoRoomConflicts {
    all disj mk1, mk2: MataKuliah |
        mk1.ruangan = mk2.ruangan => no (mk1.jadwal & mk2.jadwal)
}

// Validasi konsistensi daftar tunggu
assert WaitlistConsistency {
    all mk: MataKuliah, m: Mahasiswa |
        m in elems[mk.daftarTunggu] => mk not in m.mengambil
}
```

### Predicate untuk Skenario Testing

```alloy
// Skenario mahasiswa dengan nilai
pred studentWithGrades[m: Mahasiswa] {
    #m.mengambil >= 3
    #{mk: m.mengambil | some m.nilai[mk]} >= 2
    some mk: m.mengambil | m.nilai[mk] = A
    some mk: m.mengambil | m.nilai[mk] = B
}

// Skenario mata kuliah dengan kapasitas penuh
pred fullCapacityCourse[mk: MataKuliah] {
    #{m: Mahasiswa | mk in m.mengambil} = mk.kapasitas
    #mk.daftarTunggu > 0
}

// Skenario penjadwalan kompleks
pred complexScheduling {
    #MataKuliah >= 5
    #Ruangan >= 3
    #SlotWaktu >= 4
    some mk: MataKuliah | #mk.jadwal > 1
}
```

## Panduan Eksekusi

### Commands untuk Testing

#### 1. Testing Dasar

```alloy
// Mencari instance valid untuk registrasi
run registrasiValid for 4 but 5 Int

// Memvalidasi assertion IPK
check IPKCalculationValid for 4 but 5 Int
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Run Command untuk Validasi Registrasi**

- **Tujuan:** Mencari instance model yang memenuhi semua batasan dalam `registrasiValid`
- **Alasan Penggunaan `run`:** Command `run` mencari contoh yang memenuhi predicate, berbeda dengan `check` yang mencari counterexample
- **Mekanisme Kerja:** Alloy Analyzer akan mencoba menghasilkan status mahasiswa, mata kuliah, dan relasi yang memenuhi semua batasan
- **Hasil yang Diharapkan:** Mendapatkan contoh konkrit mahasiswa yang memiliki registrasi valid

**Step 2: Parameter Scope `for 4 but 5 Int`**

- **Tujuan:** Mengoptimalkan antara eksplorasi yang memadai dan performa analisis
- **Alasan `for 4`:** Membatasi maksimal 4 instance untuk setiap signature (Mahasiswa, MataKuliah, dll)
- **Alasan `but 5 Int`:** Mengizinkan 5 nilai integer berbeda untuk SKS, kapasitas, IPK, dll
- **Dampak Teknis:** Membatasi ruang pencarian untuk Alloy Analyzer, membuat analisis lebih feasible

**Step 3: Check Command untuk Validasi IPK**

- **Tujuan:** Memverifikasi bahwa fungsi `hitungIPK` selalu menghasilkan nilai dalam rentang yang valid
- **Alasan Penggunaan `check`:** Command `check` mencari counterexample yang melanggar assertion
- **Proses Verifikasi:** Alloy mencoba menemukan kasus dimana `hitungIPK[m] < 0` atau `hitungIPK[m] > 400`
- **Interpretasi Hasil:** Jika tidak ada counterexample, assertion terbukti valid dalam scope yang ditentukan

#### 2. Testing Skenario Spesifik

```alloy
// Testing mahasiswa dengan nilai
run studentWithGrades for 4 but 5 Int

// Testing mata kuliah penuh
run fullCapacityCourse for 4 but 5 Int

// Testing penjadwalan kompleks
run complexScheduling for 5 but 6 Int
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Testing Mahasiswa dengan Nilai**

- **Tujuan:** Memverifikasi model dapat merepresentasikan mahasiswa dengan beberapa nilai berbeda
- **Alasan Skenario:** Penting untuk validasi fungsi perhitungan IPK dan kebijakan akademik
- **Kriteria Pengujian:** Mahasiswa memiliki setidaknya 3 mata kuliah, minimal 2 dengan nilai, termasuk nilai A dan B
- **Manfaat Bisnis:** Memastikan model dapat menangani evaluasi kinerja akademik mahasiswa

**Step 2: Testing Mata Kuliah dengan Kapasitas Penuh**

- **Tujuan:** Memverifikasi model dapat menangani skenario batas kapasitas dan daftar tunggu
- **Alasan Skenario:** Situasi kapasitas penuh sering terjadi dan perlu dikelola dengan tepat
- **Kriteria Pengujian:** Mata kuliah terisi penuh (jumlah mahasiswa = kapasitas) dan memiliki daftar tunggu
- **Dampak Operasional:** Memastikan sistem dapat menangani batasan kapasitas fisik dan kebijakan waitlist

**Step 3: Testing Penjadwalan Kompleks**

- **Tujuan:** Memverifikasi model dapat menangani skenario penjadwalan yang lebih rumit
- **Alasan Peningkatan Scope:** `for 5 but 6 Int` memberikan lebih banyak ruang untuk membuat jadwal kompleks
- **Kriteria Pengujian:** Minimal 5 mata kuliah, 3 ruangan, 4 slot waktu, dan ada mata kuliah dengan multiple slot
- **Manfaat Praktis:** Memastikan model dapat menangani kompleksitas penjadwalan di dunia nyata

#### 3. Testing Fungsi IPK

```alloy
// Mencari mahasiswa dengan IPK > 0
run { some m: Mahasiswa | hitungIPK[m] > 0 } for 4 but 5 Int

// Membandingkan IPK mahasiswa
run {
    some m1, m2: Mahasiswa |
        hitungIPK[m1] > hitungIPK[m2] and
        hitungIPK[m1] > 300
} for 4 but 5 Int
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Testing Mahasiswa dengan IPK Positif**

- **Tujuan:** Memastikan model dapat menghasilkan mahasiswa dengan nilai yang dapat dihitung menjadi IPK
- **Alasan Inline Predicate:** Menggunakan expression langsung untuk kasus pengujian spesifik tanpa mendefinisikan predicate terpisah
- **Logika Query:** `some m: Mahasiswa` mencari minimal satu mahasiswa yang memenuhi kriteria
- **Hasil Ekspektasi:** Menemukan mahasiswa yang telah menyelesaikan mata kuliah dengan nilai, menghasilkan IPK > 0

**Step 2: Testing Perbandingan IPK**

- **Tujuan:** Verifikasi bahwa model dapat membedakan dan membandingkan IPK antar mahasiswa
- **Alasan Testing Perbandingan:** Penting untuk fitur perankingan dan prioritas registrasi berdasarkan IPK
- **Kriteria Kompleks:** Mencari dua mahasiswa berbeda dengan selisih IPK, dimana satu memiliki IPK > 3.0
- **Manfaat Akademik:** Memastikan model dapat menangani evaluasi perbandingan performa akademik

**Step 3: Penggunaan Angka 300 sebagai Threshold**

- **Tujuan:** Menetapkan batas minimal IPK yang bermakna (3.00) untuk testing
- **Alasan Format Integer:** 300 merepresentasikan IPK 3.00 dalam format integer yang digunakan model
- **Signifikansi Akademik:** IPK 3.00 sering menjadi batas kualifikasi untuk berbagai program akademik
- **Konsekuensi Testing:** Memverifikasi model dapat menghasilkan mahasiswa dengan performa akademik baik

#### 4. Comprehensive Testing

```alloy
// Testing dengan multiple constraints
run {
    #Mahasiswa >= 3
    #MataKuliah >= 4
    #Dosen >= 2
    some m: Mahasiswa | #m.mengambil >= 3
    some mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} > 1
} for 5 but 6 Int
```

**PENJELASAN STEP-BY-STEP:**

**Step 1: Penentuan Ukuran Minimal Universe**

- **Tujuan:** Memastikan model memiliki cukup elemen untuk testing komprehensif
- **Alasan Multiple Constraints:** Mendefinisikan batas bawah untuk jumlah entitas dalam model
- **Implementasi Kardinalitas:** `#Mahasiswa >= 3`, `#MataKuliah >= 4`, `#Dosen >= 2`
- **Manfaat Testing:** Memverifikasi model dengan populasi yang lebih realistis

**Step 2: Constraint Beban Studi**

- **Tujuan:** Memastikan model mencakup mahasiswa dengan beban studi representatif
- **Alasan Constraint:** `some m: Mahasiswa | #m.mengambil >= 3` mencari mahasiswa yang mengambil minimal 3 mata kuliah
- **Signifikansi Akademik:** 3 mata kuliah merepresentasikan beban studi normal/minimal
- **Kontribusi Testing:** Memverifikasi model dapat menangani mahasiswa dengan multiple mata kuliah

**Step 3: Constraint Popularitas Mata Kuliah**

- **Tujuan:** Memastikan model mencakup mata kuliah yang diambil oleh multiple mahasiswa
- **Alasan Constraint:** `some mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} > 1`
- **Logika Implementasi:** Mencari mata kuliah yang diambil oleh lebih dari satu mahasiswa
- **Dampak Testing:** Memverifikasi model dapat menangani mata kuliah populer dan berbagi sumber daya

**Step 4: Peningkatan Scope**

- **Tujuan:** Memberikan ruang yang cukup untuk memenuhi semua constraints
- **Alasan `for 5 but 6 Int`:** Scope yang lebih besar diperlukan untuk testing komprehensif
- **Trade-off:** Waktu eksekusi lebih lama, tetapi hasil lebih representatif
- **Best Practice:** Comprehensive testing sebaiknya menggunakan scope lebih besar dari testing dasar

### Parameter Scope Explanation

- `for 4`: Maksimal 4 instance per signature
- `but 5 Int`: Maksimal 5 nilai integer berbeda yang dapat digunakan
- Scope yang lebih besar = lebih banyak kemungkinan instance, tapi waktu eksekusi lebih lama

**PENJELASAN TEKNIS:**

**1. Signifikansi Scope dalam Alloy**

- **Tujuan:** Membatasi ruang pencarian untuk analisis yang feasible
- **Alasan Batasan:** Tanpa batasan, ruang pencarian menjadi tak terhingga
- **Implikasi:** Hasil analisis hanya valid dalam scope yang ditentukan
- **Trade-off:** Scope kecil = analisis cepat tapi kurang komprehensif; scope besar = analisis lambat tapi lebih akurat

**2. Parameter `for N`**

- **Tujuan:** Membatasi jumlah maksimal instance untuk setiap signature
- **Mekanisme:** Alloy akan mengeksplorasi model dengan 0 hingga N instance setiap signature
- **Contoh Praktis:** `for 4` berarti maksimal 4 mahasiswa, 4 mata kuliah, 4 dosen, dst.
- **Optimisasi:** Pilih nilai N yang cukup untuk representasi sistem tapi masih komputasional

**3. Parameter `but N Int`**

- **Tujuan:** Mengatur batasan khusus untuk jenis Int (bilangan bulat)
- **Alasan Pemisahan:** Integer memerlukan penanganan khusus karena sifat range numerik
- **Mekanisme:** Alloy akan menggunakan integer dari -N+1 hingga N-1
- **Contoh:** `but 5 Int` menggunakan bilangan bulat dari -4 hingga 4

### Tips Debugging

1. **Mulai dengan scope kecil** (`for 3`) untuk debugging cepat
2. **Gunakan assertion** untuk memvalidasi properti model
3. **Jalankan predicate spesifik** untuk menguji skenario tertentu
4. **Visualisasi hasil** di Alloy Analyzer untuk memahami instance yang ditemukan
5. **Iterasi perbaikan** berdasarkan counterexample yang ditemukan

**PENJELASAN TIPS DEBUGGING:**

**Tip 1: Mulai dengan Scope Kecil**

- **Tujuan:** Mempercepat iterasi awal debugging
- **Alasan Strategi:** Scope kecil menghasilkan contoh minimal yang lebih mudah dipahami
- **Implementasi Praktis:** Mulai dengan `for 3 but 4 Int` untuk debugging awal
- **Eskalasi Bertahap:** Tingkatkan scope setelah model berfungsi dengan scope kecil

**Tip 2: Gunakan Assertion**

- **Tujuan:** Memverifikasi properti penting model secara eksplisit
- **Alasan Metodologi:** Assertions menemukan kesalahan yang mungkin terlewat dalam testing biasa
- **Best Practice:** Tulis assertions untuk semua invariant kritis sistem
- **Strategi Verifikasi:** Gunakan `check` pada setiap assertion untuk mencari counterexample

**Tip 3: Jalankan Predicate Spesifik**

- **Tujuan:** Isolasi pengujian ke skenario tertentu untuk debugging yang lebih fokus
- **Alasan Efektivitas:** Mempersempit ruang pencarian ke area yang menjadi perhatian
- **Teknik Implementasi:** Definisikan predicates untuk skenario edge case atau alur bisnis spesifik
- **Manfaat Analitis:** Membantu mengidentifikasi akar masalah dalam model kompleks

**Tip 4: Visualisasi Hasil**

- **Tujuan:** Meningkatkan pemahaman tentang instance model yang dihasilkan
- **Alasan Kognitif:** Representasi visual lebih mudah dipahami daripada output teks
- **Fitur Alloy:** Gunakan proyeksi dan tema untuk menyesuaikan visualisasi
- **Teknik Analisis:** Periksa relasi dan struktur instance untuk menemukan pola atau anomali

**Tip 5: Iterasi Perbaikan**

- **Tujuan:** Meningkatkan model secara inkremental berdasarkan hasil testing
- **Metodologi:** Analisis counterexample, perbaiki model, dan uji kembali
- **Siklus Perbaikan:** Identifikasi masalah → Perbaiki constraint → Validasi kembali
- **Pendekatan Sistematis:** Catat semua counterexample dan solusinya untuk pembelajaran
