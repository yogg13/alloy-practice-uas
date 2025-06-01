# Dokumentasi Lengkap Model Alloy: Sistem Registrasi Mata Kuliah

## Daftar Isi

1. [Pendahuluan](#1-pendahuluan)
2. [Konsep Dasar Alloy](#2-konsep-dasar-alloy)
3. [Struktur Model Registrasi Mata Kuliah](#3-struktur-model-registrasi-mata-kuliah)
4. [Signatures dan Fields](#4-signatures-dan-fields)
5. [Facts dan Constraints](#5-facts-dan-constraints)
6. [Predicates dan Functions](#6-predicates-dan-functions)
7. [Assertions](#7-assertions)
8. [Run Commands](#8-run-commands)
9. [Check Commands](#9-check-commands)
10. [Tips Debugging dan Troubleshooting](#10-tips-debugging-dan-troubleshooting)
11. [Kesimpulan](#11-kesimpulan)

## 1. Pendahuluan

### 1.1 Tentang Model Ini

Model Alloy ini menggambarkan sistem registrasi mata kuliah di universitas dengan berbagai entitas dan hubungan kompleks. Model ini mencakup fitur-fitur seperti:

- Registrasi mata kuliah dengan validasi prasyarat
- Pengelolaan kapasitas ruangan dan ketersediaan fasilitas
- Perhitungan IPK berdasarkan nilai dan SKS
- Pengelolaan daftar tunggu
- Penjadwalan mata kuliah tanpa bentrok
- Kategorisasi mata kuliah dan peminatan mahasiswa

### 1.2 Tujuan Model

Model ini dibuat untuk:

- Memverifikasi aturan bisnis dalam sistem registrasi akademik
- Mendeteksi potensi masalah sebelum implementasi sistem nyata
- Memastikan integritas data dan konsistensi aturan
- Mengeksplorasi skenario edge case yang mungkin terjadi

## 2. Konsep Dasar Alloy

### 2.1 Bahasa Alloy

Alloy adalah bahasa spesifikasi berbasis logika formal yang menyediakan cara untuk menjelaskan struktur dan batasan dalam sistem. Beberapa konsep inti dalam Alloy:

- **Atoms**: Objek dasar yang tidak dapat dibagi
- **Relations**: Hubungan antara atoms
- **Signatures**: Tipe objek yang mengelompokkan atoms
- **Fields**: Relasi yang didefinisikan dalam signature
- **Facts**: Constraint yang selalu harus dipenuhi
- **Predicates**: Kondisi yang dapat dievaluasi menjadi benar atau salah
- **Functions**: Ekspresi yang menghasilkan nilai
- **Assertions**: Pernyataan yang diverifikasi melalui pencarian counterexample

### 2.2 Analisis dengan Alloy Analyzer

Alloy Analyzer bekerja dengan:

1. Mengonversi model Alloy ke formula boolean
2. Menggunakan SAT solver untuk mencari solusi
3. Memberikan visualisasi instance yang memenuhi batasan (untuk run commands)
4. Mencari counterexample untuk assertion (untuk check commands)

## 3. Struktur Model Registrasi Mata Kuliah

### 3.1 Modul dan Import

```alloy
module registrasiMataKuliah
```

**Penjelasan:**

- `module`: Keyword untuk mendeklarasikan nama modul
- `registrasiMataKuliah`: Nama modul yang berfungsi sebagai namespace
- Modul dalam Alloy seperti package dalam bahasa pemrograman lain
- Berguna untuk mengorganisir model dan memungkinkan reusability

## 4. Signatures dan Fields

### 4.1 Signature Mahasiswa

```alloy
sig Mahasiswa {
    mengambil: set MataKuliah,
    status: one StatusMahasiswa,
    semester: one Int,
    ipk: one Int,  // IPK dalam bentuk skala integer (mis. 350 = 3.50)
    peminatan: lone KategoriMK,
    nilai: MataKuliah -> lone Nilai
}
```

**Penjelasan Step-by-Step:**

1. **`sig Mahasiswa`**: Mendefinisikan signature baru bernama "Mahasiswa" yang merepresentasikan entitas mahasiswa dalam sistem
2. **`mengambil: set MataKuliah`**:

   - Field `mengambil` yang bernilai set dari MataKuliah
   - `set` menunjukkan mahasiswa bisa mengambil 0 atau lebih mata kuliah
   - Merepresentasikan mata kuliah yang sedang diambil oleh mahasiswa

3. **`status: one StatusMahasiswa`**:

   - Field `status` yang bernilai tepat satu StatusMahasiswa
   - `one` menunjukkan harus ada tepat satu nilai (tidak boleh 0 atau lebih dari 1)
   - Merepresentasikan status mahasiswa (Sarjana/Magister/Doktor)

4. **`semester: one Int`**:

   - Field `semester` yang bernilai tepat satu integer
   - Merepresentasikan semester saat ini dari mahasiswa (misalnya: 1, 2, 3, dst.)

5. **`ipk: one Int`**:

   - Field `ipk` yang bernilai tepat satu integer
   - Format khusus: nilai integer digunakan untuk merepresentasikan IPK (350 = 3.50)
   - Merepresentasikan Indeks Prestasi Kumulatif mahasiswa

6. **`peminatan: lone KategoriMK`**:

   - Field `peminatan` yang bernilai paling banyak satu KategoriMK
   - `lone` = "less than or equal to one" (0 atau 1)
   - Mahasiswa boleh tidak memiliki peminatan atau memiliki satu peminatan

7. **`nilai: MataKuliah -> lone Nilai`**:
   - Field `nilai` yang merupakan relasi dari MataKuliah ke Nilai
   - `->` adalah operator product yang membuat relasi (mapping)
   - `lone Nilai` menunjukkan setiap mata kuliah memiliki paling banyak satu nilai
   - Merepresentasikan nilai mahasiswa untuk setiap mata kuliah yang diambil

### 4.2 Signature MataKuliah

```alloy
sig MataKuliah {
    prasyarat: set MataKuliah,
    kapasitas: one Int,
    diajarOleh: one Dosen,
    jadwal: set SlotWaktu,
    sks: one Int,
    ruangan: one Ruangan,
    butuhanFasilitas: set Fasilitas,
    daftarTunggu: seq Mahasiswa,
    jenis: one JenisMK,
    kategori: set KategoriMK
}
```

**Penjelasan Step-by-Step:**

1. **`sig MataKuliah`**: Mendefinisikan signature untuk entitas mata kuliah

2. **`prasyarat: set MataKuliah`**:

   - Field `prasyarat` yang bernilai set MataKuliah
   - **Relasi refleksif**: Signature yang mereferensi dirinya sendiri
   - Merepresentasikan mata kuliah yang harus diselesaikan sebelum mengambil mata kuliah ini

3. **`kapasitas: one Int`**:

   - Field `kapasitas` yang bernilai tepat satu integer
   - Merepresentasikan jumlah maksimal mahasiswa yang dapat mengambil mata kuliah

4. **`diajarOleh: one Dosen`**:

   - Field `diajarOleh` yang bernilai tepat satu Dosen
   - Merepresentasikan dosen yang mengajar mata kuliah ini

5. **`jadwal: set SlotWaktu`**:

   - Field `jadwal` yang bernilai set SlotWaktu
   - Mata kuliah bisa memiliki beberapa slot waktu pertemuan

6. **`sks: one Int`**:

   - Field `sks` yang bernilai tepat satu integer
   - Merepresentasikan bobot SKS (Satuan Kredit Semester) mata kuliah

7. **`ruangan: one Ruangan`**:

   - Field `ruangan` yang bernilai tepat satu Ruangan
   - Merepresentasikan ruangan tempat mata kuliah dilaksanakan

8. **`butuhanFasilitas: set Fasilitas`**:

   - Field `butuhanFasilitas` yang bernilai set Fasilitas
   - Merepresentasikan fasilitas yang dibutuhkan untuk mata kuliah

9. **`daftarTunggu: seq Mahasiswa`**:

   - Field `daftarTunggu` yang bernilai sequence (urutan) dari Mahasiswa
   - **`seq`**: Berbeda dari set, sequence mempertahankan urutan dan boleh berisi duplikat
   - Merepresentasikan daftar mahasiswa yang menunggu untuk masuk ke mata kuliah yang sudah penuh

10. **`jenis: one JenisMK`**:

    - Field `jenis` yang bernilai tepat satu JenisMK
    - Merepresentasikan tipe mata kuliah (Wajib/Pilihan/UmumUniversitas)

11. **`kategori: set KategoriMK`**:
    - Field `kategori` yang bernilai set KategoriMK
    - Merepresentasikan kategori peminatan yang terkait dengan mata kuliah
    - Satu mata kuliah bisa masuk ke beberapa kategori peminatan

### 4.3 Signature Dosen dan Departemen

```alloy
sig Dosen {
    departemen: one Departemen
}

sig Departemen {}
```

**Penjelasan:**

1. **`sig Dosen`**: Mendefinisikan signature untuk entitas dosen

   - **`departemen: one Departemen`**: Setiap dosen terhubung dengan tepat satu departemen

2. **`sig Departemen {}`**: Mendefinisikan signature untuk entitas departemen
   - Tidak memiliki field, hanya digunakan sebagai identifier departemen

### 4.4 Signature SlotWaktu, Ruangan, dan Fasilitas

```alloy
sig SlotWaktu {}

sig Ruangan {
    kapasitas: one Int,
    fasilitas: set Fasilitas
}

abstract sig Fasilitas {}
one sig Proyektor, Komputer, Lab extends Fasilitas {}
```

**Penjelasan:**

1. **`sig SlotWaktu {}`**: Mendefinisikan signature untuk slot waktu perkuliahan

   - Signature kosong tanpa field, hanya digunakan untuk identifikasi

2. **`sig Ruangan`**: Mendefinisikan signature untuk ruangan

   - **`kapasitas: one Int`**: Jumlah mahasiswa maksimal yang bisa ditampung
   - **`fasilitas: set Fasilitas`**: Fasilitas yang tersedia di ruangan

3. **`abstract sig Fasilitas {}`**:

   - Signature abstract yang tidak dapat diinstansiasi langsung
   - Berfungsi sebagai "parent class" untuk tipe-tipe fasilitas

4. **`one sig Proyektor, Komputer, Lab extends Fasilitas {}`**:
   - Mendefinisikan tiga singleton signature yang meng-extend Fasilitas
   - `one sig` berarti hanya ada satu instance untuk setiap signature
   - `extends` menunjukkan inheritance (pewarisan) dari signature Fasilitas
   - Proyektor, Komputer, dan Lab adalah tiga jenis fasilitas dalam sistem

### 4.5 Abstract Signatures, Inheritance, dan Enumerations

#### Status Mahasiswa

```alloy
abstract sig StatusMahasiswa {}
one sig Sarjana, Magister, Doktor extends StatusMahasiswa {}
```

**Penjelasan:**

- `abstract sig StatusMahasiswa {}`: Signature abstract untuk mewakili status akademik
- `one sig Sarjana, Magister, Doktor extends StatusMahasiswa {}`:
  - Tiga singleton signature yang meng-extend StatusMahasiswa
  - Membuat enumerasi untuk status mahasiswa
  - Setiap status hanya memiliki tepat satu instance

#### Jenis Mata Kuliah

```alloy
abstract sig JenisMK {}
one sig Wajib, Pilihan, UmumUniversitas extends JenisMK {}
```

**Penjelasan:**

- `abstract sig JenisMK {}`: Signature abstract untuk jenis mata kuliah
- `one sig Wajib, Pilihan, UmumUniversitas extends JenisMK {}`:
  - Tiga singleton signature untuk tipe mata kuliah
  - Membuat enumerasi untuk jenis mata kuliah

#### Kategori Mata Kuliah

```alloy
sig KategoriMK {}
```

**Penjelasan:**

- `sig KategoriMK {}`: Signature untuk kategori mata kuliah (peminatan)
- Tidak abstract, sehingga bisa memiliki banyak instance
- Tidak memiliki field, hanya sebagai identifier

#### Nilai Mata Kuliah

```alloy
abstract sig Nilai {}
one sig A, B, C, D, E extends Nilai {}
```

**Penjelasan:**

- `abstract sig Nilai {}`: Signature abstract untuk nilai mata kuliah
- `one sig A, B, C, D, E extends Nilai {}`:
  - Lima singleton signature yang meng-extend Nilai
  - Membuat enumerasi untuk nilai mata kuliah

## 5. Facts dan Constraints

### 5.1 Fact KapasitasMaksimal

```alloy
fact KapasitasMaksimal {
    // Jumlah mahasiswa yang mengambil mata kuliah tidak melebihi kapasitas
    all mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} <= mk.kapasitas
}
```

**Penjelasan Step-by-Step:**

1. **`fact KapasitasMaksimal`**: Mendeklarasikan fact dengan nama yang deskriptif
2. **`all mk: MataKuliah`**: Universal quantification - untuk setiap mata kuliah
3. **`#{m: Mahasiswa | mk in m.mengambil}`**:
   - **Set comprehension**: `{m: Mahasiswa | mk in m.mengambil}` - himpunan mahasiswa yang mengambil mata kuliah `mk`
   - **`#`**: Operator cardinality (menghitung jumlah elemen dalam set)
   - Menghitung jumlah mahasiswa yang mengambil mata kuliah `mk`
4. **`<= mk.kapasitas`**: Memastikan jumlah mahasiswa tidak melebihi kapasitas mata kuliah
5. **Business Rule**: Mencegah kelebihan kapasitas dalam pendaftaran mata kuliah

### 5.2 Fact PrasyaratValid

```alloy
fact PrasyaratValid {
    // Mata kuliah tidak bisa menjadi prasyarat untuk dirinya sendiri (langsung atau tidak langsung)
    all mk: MataKuliah | mk not in mk.^prasyarat
}
```

**Penjelasan Step-by-Step:**

1. **`fact PrasyaratValid`**: Mendeklarasikan fact untuk validasi prasyarat
2. **`all mk: MataKuliah`**: Universal quantification - untuk setiap mata kuliah
3. **`mk.^prasyarat`**:
   - **`^`**: Operator transitive closure
   - Menghasilkan semua prasyarat langsung dan tidak langsung dari mata kuliah `mk`
   - Contoh: Jika A prasyarat B dan B prasyarat C, maka A dan B keduanya ada di C.^prasyarat
4. **`mk not in mk.^prasyarat`**: Memastikan mata kuliah tidak muncul dalam daftar prasyaratnya sendiri
5. **Purpose**: Mencegah circular dependency dalam struktur prasyarat

### 5.3 Fact TidakAdaBentrokJadwal

```alloy
fact TidakAdaBentrokJadwal {
    all m: Mahasiswa | all disj mk1, mk2: m.mengambil |
        no (mk1.jadwal & mk2.jadwal)
}
```

**Penjelasan Step-by-Step:**

1. **`fact TidakAdaBentrokJadwal`**: Mendeklarasikan fact untuk mencegah bentrok jadwal
2. **`all m: Mahasiswa`**: Untuk setiap mahasiswa
3. **`all disj mk1, mk2: m.mengambil`**:
   - **`disj`**: Keyword untuk distinct - mk1 dan mk2 harus berbeda
   - Untuk setiap pasangan mata kuliah berbeda yang diambil mahasiswa
4. **`no (mk1.jadwal & mk2.jadwal)`**:
   - **`&`**: Operator intersection (irisan)
   - **`mk1.jadwal & mk2.jadwal`**: Slot waktu yang sama antara dua mata kuliah
   - **`no`**: Quantifier yang berarti "tidak ada" elemen dalam hasil
5. **Purpose**: Memastikan tidak ada mahasiswa yang mengambil dua mata kuliah dengan jadwal yang bentrok

### 5.4 Fact PersyaratanPeminatan

```alloy
fact PersyaratanPeminatan {
    all m: Mahasiswa | some m.peminatan implies
        #{mk: m.mengambil | m.peminatan in mk.kategori} >= 3
}
```

**Penjelasan Step-by-Step:**

1. **`fact PersyaratanPeminatan`**: Mendeklarasikan fact untuk aturan peminatan
2. **`all m: Mahasiswa`**: Untuk setiap mahasiswa
3. **`some m.peminatan implies`**:
   - **`some m.peminatan`**: Mahasiswa memiliki peminatan (tidak null)
   - **`implies`**: Operator implikasi logis (jika... maka...)
4. **`#{mk: m.mengambil | m.peminatan in mk.kategori} >= 3`**:
   - **Set comprehension**: Mata kuliah yang diambil mahasiswa yang kategorinya termasuk peminatan mahasiswa
   - **`#`**: Menghitung jumlah mata kuliah tersebut
   - Harus minimal 3 mata kuliah
5. **Purpose**: Memastikan mahasiswa yang memilih peminatan mengambil minimal 3 mata kuliah di peminatan tersebut

### 5.5 Fact KetersediaanRuangan

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

**Penjelasan Step-by-Step:**

1. **Constraint pertama - Kapasitas ruangan**:

   - **`all mk: MataKuliah`**: Untuk setiap mata kuliah
   - **`mk.ruangan.kapasitas`**: Kapasitas ruangan tempat mata kuliah diselenggarakan
   - **`>= #{m: Mahasiswa | mk in m.mengambil}`**: Harus lebih besar atau sama dengan jumlah mahasiswa yang mengambil mata kuliah

2. **Constraint kedua - Fasilitas tersedia**:

   - **`all mk: MataKuliah`**: Untuk setiap mata kuliah
   - **`mk.butuhanFasilitas in mk.ruangan.fasilitas`**:
     - **`in`**: Operator subset - semua elemen di sisi kiri harus ada di sisi kanan
     - Semua fasilitas yang dibutuhkan oleh mata kuliah harus tersedia di ruangan

3. **Constraint ketiga - Tidak ada bentrok ruangan**:
   - **`all r: Ruangan, t: SlotWaktu`**: Untuk setiap pasangan ruangan dan slot waktu
   - **`lone mk: MataKuliah | mk.ruangan = r and t in mk.jadwal`**:
     - **`lone`**: Paling banyak satu mata kuliah
     - **`mk.ruangan = r and t in mk.jadwal`**: Mata kuliah yang menggunakan ruangan r pada slot waktu t
     - Memastikan tidak ada dua mata kuliah yang menggunakan ruangan yang sama pada waktu yang sama

### 5.6 Fact AturanDaftarTunggu

```alloy
fact AturanDaftarTunggu {
    all mk: MataKuliah | all m: elems[mk.daftarTunggu] |
        m not in {mhs: Mahasiswa | mk in mhs.mengambil}
}
```

**Penjelasan Step-by-Step:**

1. **`fact AturanDaftarTunggu`**: Mendeklarasikan fact untuk aturan daftar tunggu
2. **`all mk: MataKuliah`**: Untuk setiap mata kuliah
3. **`all m: elems[mk.daftarTunggu]`**:
   - **`elems[...]`**: Mengambil elemen-elemen dalam sequence
   - Untuk setiap mahasiswa dalam daftar tunggu mata kuliah
4. **`m not in {mhs: Mahasiswa | mk in mhs.mengambil}`**:
   - **Set comprehension**: `{mhs: Mahasiswa | mk in mhs.mengambil}` - mahasiswa yang sudah mengambil mata kuliah
   - **`not in`**: Memastikan mahasiswa tidak ada dalam set tersebut
5. **Purpose**: Memastikan mahasiswa dalam daftar tunggu tidak sedang mengambil mata kuliah yang sama

### 5.7 Fact BebanKerjaDosen

```alloy
fact BebanKerjaDosen {
    // Tidak ada dosen yang mengajar lebih dari 3 mata kuliah
    all d: Dosen | #{mk: MataKuliah | mk.diajarOleh = d} <= 3

    // Total SKS yang diajarkan tidak melebihi batas
    all d: Dosen | (sum mk: MataKuliah | mk.diajarOleh = d => mk.sks else 0) <= 12
}
```

**Penjelasan Step-by-Step:**

1. **Constraint pertama - Batas jumlah mata kuliah**:

   - **`all d: Dosen`**: Untuk setiap dosen
   - **`#{mk: MataKuliah | mk.diajarOleh = d} <= 3`**:
     - **Set comprehension**: `{mk: MataKuliah | mk.diajarOleh = d}` - mata kuliah yang diajar oleh dosen d
     - **`#`**: Menghitung jumlah mata kuliah tersebut
     - Harus kurang dari atau sama dengan 3

2. **Constraint kedua - Batas total SKS**:
   - **`all d: Dosen`**: Untuk setiap dosen
   - **`(sum mk: MataKuliah | mk.diajarOleh = d => mk.sks else 0) <= 12`**:
     - **`sum`**: Operator penjumlahan
     - **`mk.diajarOleh = d => mk.sks else 0`**: Jika mata kuliah diajar oleh dosen d, hitung SKSnya, jika tidak bernilai 0
     - Total SKS yang diajar dosen harus kurang dari atau sama dengan 12

### 5.8 Fact BatasanNilai

```alloy
fact BatasanNilai {
    all m: Mahasiswa | m.nilai.univ in m.mengambil
}
```

**Penjelasan Step-by-Step:**

1. **`fact BatasanNilai`**: Mendeklarasikan fact untuk batasan nilai
2. **`all m: Mahasiswa`**: Untuk setiap mahasiswa
3. **`m.nilai.univ in m.mengambil`**:
   - **`m.nilai.univ`**: Domain dari relasi nilai mahasiswa (mata kuliah yang memiliki nilai)
   - **`in m.mengambil`**: Subset dari mata kuliah yang diambil
   - Memastikan mahasiswa hanya memiliki nilai untuk mata kuliah yang diambil
4. **Purpose**: Menjaga integritas data nilai - tidak boleh ada nilai untuk mata kuliah yang tidak diambil

## 6. Predicates dan Functions

### 6.1 Predicate registrasiValid

```alloy
pred registrasiValid[m: Mahasiswa] {
    // Mahasiswa tidak mengambil lebih dari 5 mata kuliah
    #(m.mengambil) <= 5

    // Semua prasyarat terpenuhi
    all mk: m.mengambil | all pr: mk.prasyarat | pr in m.mengambil

    // Maksimum SKS per semester
    (sum mk: m.mengambil | mk.sks) <= 24
}
```

**Penjelasan Step-by-Step:**

1. **`pred registrasiValid[m: Mahasiswa]`**:

   - Mendeklarasikan predicate dengan nama "registrasiValid"
   - Parameter: satu mahasiswa (`m: Mahasiswa`)

2. **Constraint pertama - Batas jumlah mata kuliah**:

   - **`#(m.mengambil) <= 5`**:
     - **`#`**: Operator cardinality (menghitung jumlah elemen)
     - Mahasiswa tidak boleh mengambil lebih dari 5 mata kuliah

3. **Constraint kedua - Validasi prasyarat**:

   - **`all mk: m.mengambil | all pr: mk.prasyarat | pr in m.mengambil`**:
     - **Nested universal quantification** - untuk setiap mata kuliah yang diambil dan setiap prasyaratnya
     - Semua prasyarat harus sudah diambil oleh mahasiswa

4. **Constraint ketiga - Batas SKS**:
   - **`(sum mk: m.mengambil | mk.sks) <= 24`**:
     - **`sum`**: Operator agregasi untuk menjumlahkan nilai
     - Total SKS mata kuliah yang diambil tidak boleh melebihi 24

### 6.2 Predicate prioritasRegistrasi

```alloy
pred prioritasRegistrasi[m1, m2: Mahasiswa] {
    m1.semester > m2.semester or
    (m1.semester = m2.semester and m1.ipk > m2.ipk)
}
```

**Penjelasan Step-by-Step:**

1. **`pred prioritasRegistrasi[m1, m2: Mahasiswa]`**:

   - Mendeklarasikan predicate dengan nama "prioritasRegistrasi"
   - Parameters: dua mahasiswa (`m1, m2: Mahasiswa`)

2. **Kondisi prioritas**:

   - **`m1.semester > m2.semester`**: Mahasiswa dengan semester lebih tinggi memiliki prioritas
   - **`or`**: Operator disjunction (OR) - salah satu kondisi harus benar
   - **`(m1.semester = m2.semester and m1.ipk > m2.ipk)`**:
     - Jika semester sama, mahasiswa dengan IPK lebih tinggi memiliki prioritas
     - **`and`**: Operator conjunction (AND) - kedua kondisi harus benar

3. **Purpose**: Menentukan prioritas antara dua mahasiswa untuk keperluan registrasi atau daftar tunggu

### 6.3 Function mataKuliahPerDepartemen

```alloy
fun mataKuliahPerDepartemen[d: Departemen]: set MataKuliah {
    {mk: MataKuliah | mk.diajarOleh.departemen = d}
}
```

**Penjelasan Step-by-Step:**

1. **`fun mataKuliahPerDepartemen[d: Departemen]: set MataKuliah`**:

   - Mendeklarasikan function dengan nama "mataKuliahPerDepartemen"
   - Parameter: satu departemen (`d: Departemen`)
   - Return type: `set MataKuliah` - mengembalikan set mata kuliah

2. **Body function**:

   - **`{mk: MataKuliah | mk.diajarOleh.departemen = d}`**:
     - **Set comprehension**: Membuat set mata kuliah yang memenuhi kondisi
     - **`mk.diajarOleh.departemen = d`**: Mata kuliah yang diajarkan oleh dosen dari departemen d
     - **Chain navigation**: `mk` → `diajarOleh` (dosen) → `departemen`

3. **Purpose**: Mendapatkan semua mata kuliah yang diajarkan oleh dosen dari departemen tertentu

### 6.4 Function hitungIPK

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
                sksD = sum mk: {mk: mksWithGrades | m.nilai[mk] = D} | mk.sks |

            let totalPoints = add[add[add[mul[sksA, 4], mul[sksB, 3]], mul[sksC, 2]], sksD] |
                // Hitung IPK dengan format integer (350 = 3.50)
                div[mul[totalPoints, 100], totalSKS]
        )
    )
}
```

**Penjelasan Step-by-Step:**

1. **`fun hitungIPK[m: Mahasiswa]: Int`**:

   - Mendeklarasikan function dengan nama "hitungIPK"
   - Parameter: satu mahasiswa (`m: Mahasiswa`)
   - Return type: `Int` - mengembalikan nilai integer (untuk IPK dikalikan 100)

2. **Let Expression untuk mata kuliah dengan nilai**:

   - **`let mksWithGrades = {mk: m.mengambil | some m.nilai[mk]} |`**:
     - **`let`**: Keyword untuk binding variabel lokal
     - **Set comprehension**: Mata kuliah yang diambil DAN memiliki nilai
     - **`some m.nilai[mk]`**: Memfilter mata kuliah yang memiliki nilai

3. **Conditional Return - Jika tidak ada mata kuliah dengan nilai**:

   - **`#mksWithGrades = 0 => 0 else (...)`**:
     - **`=>`**: Operator if-then
     - Jika tidak ada mata kuliah dengan nilai, IPK = 0

4. **Let Expression untuk total SKS**:

   - **`let totalSKS = sum mk: mksWithGrades | mk.sks |`**:
     - **`sum`**: Operator agregasi untuk menjumlahkan nilai
     - Menjumlahkan SKS dari semua mata kuliah yang memiliki nilai

5. **Conditional Return - Jika total SKS = 0**:

   - **`totalSKS = 0 => 0 else (...)`**:
     - Guard clause untuk menghindari division by zero
     - Jika total SKS = 0, kembalikan 0

6. **Let Expression untuk SKS per kategori nilai**:

   - **`let sksA = sum mk: {mk: mksWithGrades | m.nilai[mk] = A} | mk.sks,`**:
     - Total SKS mata kuliah dengan nilai A
   - **`sksB, sksC, sksD`**: Total SKS untuk mata kuliah dengan nilai B, C, D
   - Mata kuliah dengan nilai E tidak dihitung (memiliki poin 0)

7. **Let Expression untuk total poin**:

   - **`let totalPoints = add[add[add[mul[sksA, 4], mul[sksB, 3]], mul[sksC, 2]], sksD] |`**:
     - **`mul[sksA, 4]`**: SKS dengan nilai A × 4 poin
     - **`mul[sksB, 3]`**: SKS dengan nilai B × 3 poin
     - **`mul[sksC, 2]`**: SKS dengan nilai C × 2 poin
     - **`sksD`**: SKS dengan nilai D × 1 poin (implisit)
     - **`add`**: Fungsi untuk penjumlahan

8. **Perhitungan IPK final**:
   - **`div[mul[totalPoints, 100], totalSKS]`**:
     - **`mul[totalPoints, 100]`**: Mengalikan total poin dengan 100 untuk format integer
     - **`div[..., totalSKS]`**: Membagi dengan total SKS
     - Hasil: 350 = IPK 3.50, 400 = IPK 4.00, dll.

## 7. Assertions

### 7.1 Assertion IPKCalculationValid

```alloy
assert IPKCalculationValid {
    // IPK yang dihitung harus dalam rentang yang wajar (0-400 untuk skala 4.00)
    all m: Mahasiswa | hitungIPK[m] >= 0 and hitungIPK[m] <= 400
}
```

**Penjelasan Step-by-Step:**

1. **`assert IPKCalculationValid`**: Mendeklarasikan assertion dengan nama "IPKCalculationValid"
2. **`all m: Mahasiswa`**: Universal quantification - untuk setiap mahasiswa
3. **`hitungIPK[m] >= 0 and hitungIPK[m] <= 400`**:
   - IPK yang dihitung tidak boleh negatif
   - IPK tidak boleh melebihi 400 (4.00)
   - **`and`**: Keduanya harus terpenuhi
4. **Purpose**: Memverifikasi bahwa fungsi hitungIPK menghasilkan nilai yang masuk akal

### 7.2 Assertion PrerequisitesEnforced

```alloy
assert PrerequisitesEnforced {
    // Jika mahasiswa mengambil mata kuliah dan registrasi valid, semua prasyaratnya harus dipenuhi
    all m: Mahasiswa | registrasiValid[m] implies
        all mk: m.mengambil, prereq: mk.prasyarat | prereq in m.mengambil
}
```

**Penjelasan Step-by-Step:**

1. **`assert PrerequisitesEnforced`**: Mendeklarasikan assertion untuk memeriksa penegakan prasyarat
2. **`all m: Mahasiswa`**: Untuk setiap mahasiswa
3. **`registrasiValid[m] implies`**:
   - **`implies`**: Operator implikasi logika (jika... maka...)
   - Jika registrasi mahasiswa valid, maka...
4. **`all mk: m.mengambil, prereq: mk.prasyarat | prereq in m.mengambil`**:
   - **Multi-variable universal quantification**: Untuk setiap mata kuliah yang diambil dan setiap prasyaratnya
   - **`prereq in m.mengambil`**: Prasyarat harus termasuk dalam mata kuliah yang diambil
5. **Purpose**: Memverifikasi bahwa mahasiswa dengan registrasi valid selalu memenuhi semua prasyarat

### 7.3 Assertion NoRoomConflicts

```alloy
assert NoRoomConflicts {
    // Tidak ada dua mata kuliah yang menggunakan ruangan yang sama pada waktu yang sama
    all disj mk1, mk2: MataKuliah |
        mk1.ruangan = mk2.ruangan => no (mk1.jadwal & mk2.jadwal)
}
```

**Penjelasan Step-by-Step:**

1. **`assert NoRoomConflicts`**: Mendeklarasikan assertion untuk memeriksa konflik ruangan
2. **`all disj mk1, mk2: MataKuliah`**:
   - Untuk setiap pasangan mata kuliah berbeda
   - **`disj`**: Memastikan mk1 dan mk2 adalah mata kuliah yang berbeda
3. **`mk1.ruangan = mk2.ruangan => no (mk1.jadwal & mk2.jadwal)`**:
   - **`=>`**: Operator implikasi (jika... maka...)
   - Jika dua mata kuliah menggunakan ruangan yang sama
   - **`no (mk1.jadwal & mk2.jadwal)`**: Tidak boleh ada slot waktu yang sama
4. **Purpose**: Memverifikasi bahwa tidak ada konflik penggunaan ruangan

### 7.4 Assertion WaitlistConsistency

```alloy
assert WaitlistConsistency {
    // Mahasiswa di daftar tunggu tidak sedang mengambil mata kuliah tersebut
    all mk: MataKuliah, m: Mahasiswa |
        m in elems[mk.daftarTunggu] => mk not in m.mengambil
}
```

**Penjelasan Step-by-Step:**

1. **`assert WaitlistConsistency`**: Mendeklarasikan assertion untuk memeriksa konsistensi daftar tunggu
2. **`all mk: MataKuliah, m: Mahasiswa`**: Untuk setiap mata kuliah dan setiap mahasiswa
3. **`m in elems[mk.daftarTunggu] => mk not in m.mengambil`**:
   - **`elems[mk.daftarTunggu]`**: Mengambil elemen-elemen dalam sequence daftar tunggu
   - **`=>`**: Jika mahasiswa dalam daftar tunggu mata kuliah
   - **`mk not in m.mengambil`**: Maka mahasiswa tidak boleh mengambil mata kuliah tersebut
4. **Purpose**: Memverifikasi bahwa mahasiswa tidak bisa sekaligus mengambil mata kuliah dan berada di daftar tunggu

### 7.5 Assertion GradeConsistency

```alloy
assert GradeConsistency {
    // Mahasiswa hanya memiliki nilai untuk mata kuliah yang diambil
    all m: Mahasiswa | m.nilai.univ in m.mengambil
}
```

**Penjelasan Step-by-Step:**

1. **`assert GradeConsistency`**: Mendeklarasikan assertion untuk memeriksa konsistensi nilai
2. **`all m: Mahasiswa`**: Untuk setiap mahasiswa
3. **`m.nilai.univ in m.mengambil`**:
   - **`m.nilai.univ`**: Domain dari relasi nilai (mata kuliah yang memiliki nilai)
   - **`in m.mengambil`**: Subset dari mata kuliah yang diambil mahasiswa
4. **Purpose**: Memverifikasi bahwa mahasiswa hanya memiliki nilai untuk mata kuliah yang diambil

### 7.6 Assertion InstructorWorkloadValid

```alloy
assert InstructorWorkloadValid {
    // Beban kerja dosen tidak melebihi batas
    all d: Dosen |
        #{mk: MataKuliah | mk.diajarOleh = d} <= 3 and
        (sum mk: MataKuliah | mk.diajarOleh = d => mk.sks else 0) <= 12
}
```

**Penjelasan Step-by-Step:**

1. **`assert InstructorWorkloadValid`**: Mendeklarasikan assertion untuk memeriksa beban kerja dosen
2. **`all d: Dosen`**: Untuk setiap dosen
3. **`#{mk: MataKuliah | mk.diajarOleh = d} <= 3`**:
   - Jumlah mata kuliah yang diajar dosen tidak lebih dari 3
4. **`and`**: Kedua kondisi harus dipenuhi
5. **`(sum mk: MataKuliah | mk.diajarOleh = d => mk.sks else 0) <= 12`**:
   - Total SKS yang diajar dosen tidak lebih dari 12
6. **Purpose**: Memverifikasi bahwa beban kerja dosen sesuai dengan batasan yang ditetapkan

## 8. Run Commands

### 8.1 Basic Run Commands

```alloy
run { some Mahasiswa } for 5 but 6 Int //apakah bisa membuat mahasiswa
run { some MataKuliah } for 5 but 6 Int // Memperbesar scope untuk memungkinkan instance ditemukan
run { some m: Mahasiswa | some m.mengambil } for 5 but 6 Int // Memastikan mahasiswa mengambil setidaknya satu mata kuliah
```

**Penjelasan Step-by-Step:**

1. **`run { some Mahasiswa }`**:

   - **Run command**: Meminta Alloy untuk mencari instance yang memenuhi formula
   - **`some Mahasiswa`**: Ada setidaknya satu mahasiswa dalam model
   - **Purpose**: Memverifikasi bahwa model bisa membuat instance mahasiswa

2. **`for 5 but 6 Int`**:

   - **`for 5`**: Scope 5 - maksimal 5 atom untuk setiap signature
   - **`but 6 Int`**: Override bitwidth integer menjadi 6 bit
   - **Bitwidth 6**: Range integer -32 sampai 31

3. **`run { some MataKuliah }`**:

   - Memverifikasi bisa membuat instance mata kuliah

4. **`run { some m: Mahasiswa | some m.mengambil }`**:
   - Memverifikasi bisa membuat mahasiswa yang mengambil setidaknya satu mata kuliah

### 8.2 Run Commands dengan Predicate

```alloy
run { some m: Mahasiswa | registrasiValid[m] } for 6 but 6 Int //melihat instance registrasi yang valid - scope diperbesar
```

**Penjelasan:**

- Mencari instance di mana ada mahasiswa dengan registrasi valid
- Menggunakan predicate `registrasiValid` yang didefinisikan sebelumnya
- Scope diperbesar menjadi 6 untuk menemukan instance yang valid

### 8.3 Run Commands untuk Testing Scenario

```alloy
run studentWithGrades for 4 but 5 Int //scenario dengan mahasiswa yang memiliki nilai
run fullCapacityCourse for 4 but 5 Int //scenario dengan mata kuliah penuh
run complexScheduling for 5 but 6 Int //scenario penjadwalan kompleks
```

**Penjelasan:**

1. **`run studentWithGrades`**:

   - Menggunakan predicate studentWithGrades (didefinisikan di bagian lain)
   - Mencari mahasiswa dengan nilai A dan B untuk beberapa mata kuliah

2. **`run fullCapacityCourse`**:

   - Mencari mata kuliah dengan kapasitas penuh dan daftar tunggu

3. **`run complexScheduling`**:
   - Mencari skenario penjadwalan dengan banyak mata kuliah dan ruangan

### 8.4 Complex Run Commands

```alloy
run {
    some m: Mahasiswa |
        some mk: m.mengambil | some m.nilai[mk] and m.ipk > 0
} for 6 but 7 Int // Test fungsi hitungIPK dengan target yang lebih realistis
```

**Penjelasan Step-by-Step:**

1. **`some m: Mahasiswa`**: Ada setidaknya satu mahasiswa
2. **`some mk: m.mengambil`**: Mahasiswa mengambil setidaknya satu mata kuliah
3. **`some m.nilai[mk]`**: Mahasiswa memiliki nilai untuk mata kuliah tersebut
4. **`and m.ipk > 0`**: IPK mahasiswa lebih dari 0 (artinya berhasil dihitung)
5. **Purpose**: Menguji fungsi hitungIPK dengan data realistis

```alloy
run {
    #Mahasiswa >= 3
    #MataKuliah >= 4
    #Dosen >= 2
    some m: Mahasiswa | #m.mengambil >= 3
    some mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} > 1
} for 5 but 6 Int //Comprehensive test dengan banyak constraints
```

**Penjelasan Multi-constraints:**

1. Minimal 3 mahasiswa dalam model
2. Minimal 4 mata kuliah
3. Minimal 2 dosen
4. Setidaknya ada mahasiswa yang mengambil 3 mata kuliah atau lebih
5. Setidaknya ada mata kuliah yang diambil oleh lebih dari 1 mahasiswa

## 9. Check Commands

```alloy
check IPKCalculationValid for 5 but 6 Int //Check IPK calculation validity
check PrerequisitesEnforced for 5 but 6 Int //Check prerequisites enforcement dengan scope lebih besar
check NoRoomConflicts for 4 but 5 Int  //Check room conflicts
check WaitlistConsistency for 4 but 5 Int //Check waitlist consistency
check GradeConsistency for 4 but 5 Int //Check grade consistency
check InstructorWorkloadValid for 4 but 5 Int //Check instructor workload
```

**Penjelasan Step-by-Step:**

1. **`check IPKCalculationValid for 5 but 6 Int`**:

   - **`check`**: Command untuk mencari counterexample dari assertion
   - **`IPKCalculationValid`**: Assertion yang diperiksa (IPK harus dalam range yang valid)
   - **`for 5 but 6 Int`**: Scope 5 dengan bitwidth integer 6
   - **Purpose**: Memeriksa apakah fungsi hitungIPK selalu menghasilkan nilai dalam rentang yang valid

2. **`check PrerequisitesEnforced for 5 but 6 Int`**:

   - Memeriksa apakah prasyarat selalu dipenuhi ketika registrasi valid
   - Menggunakan scope yang lebih besar (5) untuk verifikasi yang lebih kuat

3. **`check NoRoomConflicts for 4 but 5 Int`**:

   - Memeriksa tidak ada konflik penggunaan ruangan
   - Scope 4 dengan bitwidth 5

4. **`check WaitlistConsistency for 4 but 5 Int`**:

   - Memeriksa konsistensi daftar tunggu
   - Memastikan mahasiswa tidak bisa berada di daftar tunggu mata kuliah yang diambil

5. **`check GradeConsistency for 4 but 5 Int`**:

   - Memeriksa mahasiswa hanya memiliki nilai untuk mata kuliah yang diambil

6. **`check InstructorWorkloadValid for 4 but 5 Int`**:
   - Memeriksa beban kerja dosen sesuai batasan

## 10. Tips Debugging dan Troubleshooting

### 10.1 Mengatasi "No Instance Found"

Ketika run command gagal menemukan instance:

1. **Peningkatan Scope**: Tingkatkan nilai scope dan bitwidth

   ```alloy
   run predicate for 6 but 7 Int
   ```

2. **Analisis Constraints**:

   - Identifikasi constraints yang mungkin bertentangan
   - Coba run command dengan subset dari constraints

3. **Relaxasi Constraints**:
   - Lemahkan constraints yang terlalu ketat
   - Gunakan `some` atau `>=` daripada `all` atau `=`

### 10.2 Mengatasi Assertion Check Failures

Ketika assertion check menghasilkan counterexample:

1. **Analisis Counterexample**:

   - Tinjau instance yang menyebabkan assertion gagal
   - Pahami kenapa instance ini melanggar assertion

2. **Perbaiki Model atau Assertion**:

   ```alloy
   // Assertion yang diperkuat
   assert PrerequisitesEnforced {
     all m: Mahasiswa | registrasiValid[m] implies
       all mk: m.mengambil, prereq: mk.prasyarat | prereq in m.mengambil
   }
   ```

3. **Verifikasi Kembali**:
   ```alloy
   check PrerequisitesEnforced for 5 but 6 Int
   ```

### 10.3 Optimasi Performance

Untuk model yang kompleks:

1. **Gunakan Scope Minimal Namun Cukup**:

   ```alloy
   check assertion for 3 but 4 Int
   ```

2. **Parsimony dalam Constraints**:

   - Hindari constraints berlebihan yang tidak diperlukan
   - Pertimbangkan tradeoff antara akurasi dan performance

3. **Refaktor untuk Performance**:
   - Bagi model besar menjadi modul-modul terpisah
   - Gunakan teknik inkremental model building

## 11. Kesimpulan

Model Alloy untuk sistem registrasi mata kuliah ini mendemonstrasikan kemampuan Alloy dalam memodelkan sistem kompleks dengan banyak entitas dan relasi. Beberapa poin penting:

1. **Structural Modeling**:

   - Signatures dan fields menangkap struktur statis sistem
   - Relasi refleksif (prasyarat) dan multi-relasi (nilai) ditangani dengan baik

2. **Business Rules**:

   - Facts menjamin integritas data dan batasan bisnis
   - Predicates memungkinkan validasi fleksibel

3. **Verification**:

   - Assertions memverifikasi properti kompleks seperti non-sirkularitas prasyarat
   - Check commands memastikan model sesuai ekspektasi

4. **Expressiveness**:
   - Ekspresi relasional (join, product, closure) memungkinkan query kompleks
   - Quantifiers (`all`, `some`, `no`, `lone`) memberikan fleksibilitas logika

Model ini bisa digunakan sebagai blueprint untuk implementasi sistem registrasi mata kuliah nyata, dengan jaminan formal bahwa aturan bisnis dipatuhi dan edge cases ditangani dengan tepat.
