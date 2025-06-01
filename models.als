        module registrasiMataKuliah

        // Definisi signature
        sig Mahasiswa {
            mengambil: set MataKuliah,
            status: one StatusMahasiswa,
            semester: one Int,
            ipk: one Int,  // IPK dalam bentuk skala integer (mis. 350 = 3.50)
            peminatan: lone KategoriMK,
            nilai: MataKuliah -> lone Nilai
        }

        sig MataKuliah {
            prasyarat: set MataKuliah,
            kapasitas: one Int,
            diajarOleh: one Dosen,
            jadwal: set SlotWaktu,  // Field baru
            sks: one Int,  // Jumlah SKS
            ruangan: one Ruangan,
            butuhanFasilitas: set Fasilitas,
            daftarTunggu: seq Mahasiswa,
            jenis: one JenisMK,
            kategori: set KategoriMK
        }

        sig Dosen {
            departemen: one Departemen
        }

        sig Departemen {}

        sig SlotWaktu {}

        sig Ruangan {
            kapasitas: one Int,
            fasilitas: set Fasilitas
        }

        abstract sig Fasilitas {}
        one sig Proyektor, Komputer, Lab extends Fasilitas {}

        // Klasifikasi mahasiswa
        abstract sig StatusMahasiswa {}
        one sig Sarjana, Magister, Doktor extends StatusMahasiswa {}

        // Jenis mata kuliah
        abstract sig JenisMK {}
        one sig Wajib, Pilihan, UmumUniversitas extends JenisMK {}

        // Kategori mata kuliah untuk peminatan
        sig KategoriMK {}

        // Nilai mata kuliah
        abstract sig Nilai {}
        one sig A, B, C, D, E extends Nilai {}

        // Fakta-fakta dasar
        fact KapasitasMaksimal {
            // Jumlah mahasiswa yang mengambil mata kuliah tidak melebihi kapasitas
            all mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} <= mk.kapasitas
        }

        fact PrasyaratValid {
            // Mata kuliah tidak bisa menjadi prasyarat untuk dirinya sendiri (langsung atau tidak langsung)
            all mk: MataKuliah | mk not in mk.^prasyarat
        }

        fact TidakAdaBentrokJadwal {
            all m: Mahasiswa | all disj mk1, mk2: m.mengambil | 
                no (mk1.jadwal & mk2.jadwal)
        }

        // Persyaratan peminatan
        fact PersyaratanPeminatan {
            all m: Mahasiswa | some m.peminatan implies
                #{mk: m.mengambil | m.peminatan in mk.kategori} >= 3
        }

        // Predikat
        pred registrasiValid[m: Mahasiswa] {
            // Mahasiswa tidak mengambil lebih dari 5 mata kuliah
            #(m.mengambil) <= 5
            
            // Semua prasyarat terpenuhi
            all mk: m.mengambil | all pr: mk.prasyarat | pr in m.mengambil

            // Maksimum SKS per semester
            (sum mk: m.mengambil | mk.sks) <= 24
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

        // Batasan ketersediaan ruangan
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

        // Aturan daftar tunggu
        fact AturanDaftarTunggu {
            all mk: MataKuliah | all m: elems[mk.daftarTunggu] |
                m not in {mhs: Mahasiswa | mk in mhs.mengambil}
        }        // Prioritas registrasi berdasarkan semester dan IPK
        pred prioritasRegistrasi[m1, m2: Mahasiswa] {
            m1.semester > m2.semester or
            (m1.semester = m2.semester and m1.ipk > m2.ipk)
        }

        // Tambahkan beban kerja maksimal untuk dosen
        fact BebanKerjaDosen {
            // Tidak ada dosen yang mengajar lebih dari 3 mata kuliah
            all d: Dosen | #{mk: MataKuliah | mk.diajarOleh = d} <= 3
            
            // Total SKS yang diajarkan tidak melebihi batas
            all d: Dosen | (sum mk: MataKuliah | mk.diajarOleh = d => mk.sks else 0) <= 12
        }

        // Batasan nilai hanya untuk mata kuliah yang diambil
        fact BatasanNilai {
            all m: Mahasiswa | m.nilai.univ in m.mengambil        }

        // Fungsi untuk menghitung IPK
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

// Assertion tambahan untuk memvalidasi model
assert IPKCalculationValid {
    // IPK yang dihitung harus dalam rentang yang wajar (0-400 untuk skala 4.00)
    all m: Mahasiswa | hitungIPK[m] >= 0 and hitungIPK[m] <= 400
}

assert PrerequisitesEnforced {
    // Jika mahasiswa mengambil mata kuliah, semua prasyaratnya harus dipenuhi
    all m: Mahasiswa, mk: m.mengambil | 
        all prereq: mk.prasyarat | prereq in m.mengambil
}

assert NoRoomConflicts {
    // Tidak ada dua mata kuliah yang menggunakan ruangan yang sama pada waktu yang sama
    all disj mk1, mk2: MataKuliah | 
        mk1.ruangan = mk2.ruangan => no (mk1.jadwal & mk2.jadwal)
}

assert WaitlistConsistency {
    // Mahasiswa di daftar tunggu tidak sedang mengambil mata kuliah tersebut
    all mk: MataKuliah, m: Mahasiswa | 
        m in elems[mk.daftarTunggu] => mk not in m.mengambil
}

assert GradeConsistency {
    // Mahasiswa hanya memiliki nilai untuk mata kuliah yang diambil
    all m: Mahasiswa | m.nilai.univ in m.mengambil
}

assert InstructorWorkloadValid {
    // Beban kerja dosen tidak melebihi batas
    all d: Dosen | 
        #{mk: MataKuliah | mk.diajarOleh = d} <= 3 and
        (sum mk: MataKuliah | mk.diajarOleh = d => mk.sks else 0) <= 12
}

// Predicate untuk testing scenarios
pred studentWithGrades[m: Mahasiswa] {
    // Mahasiswa memiliki beberapa mata kuliah dengan nilai
    #m.mengambil >= 3
    #{mk: m.mengambil | some m.nilai[mk]} >= 2
    some mk: m.mengambil | m.nilai[mk] = A
    some mk: m.mengambil | m.nilai[mk] = B
}

pred fullCapacityCourse[mk: MataKuliah] {
    // Mata kuliah dengan kapasitas penuh
    #{m: Mahasiswa | mk in m.mengambil} = mk.kapasitas
    #mk.daftarTunggu > 0
}

pred complexScheduling {
    // Skenario penjadwalan yang kompleks
    #MataKuliah >= 5
    #Ruangan >= 3
    #SlotWaktu >= 4
    some mk: MataKuliah | #mk.jadwal > 1  // Mata kuliah dengan multiple slot waktu
}

// Commands untuk menjalankan dan memvalidasi model
// 1. Command dasar untuk melihat instance valid
run registrasiValid for 4 but 5 Int

// 2. Check assertion IPK calculation
check IPKCalculationValid for 4 but 5 Int

// 3. Check prerequisite enforcement
check PrerequisitesEnforced for 4 but 5 Int

// 4. Check room conflicts
check NoRoomConflicts for 4 but 5 Int

// 5. Check waitlist consistency
check WaitlistConsistency for 4 but 5 Int

// 6. Check grade consistency
check GradeConsistency for 4 but 5 Int

// 7. Check instructor workload
check InstructorWorkloadValid for 4 but 5 Int

// 8. Run scenario dengan mahasiswa yang memiliki nilai
run studentWithGrades for 4 but 5 Int

// 9. Run scenario dengan mata kuliah penuh
run fullCapacityCourse for 4 but 5 Int

// 10. Run scenario penjadwalan kompleks
run complexScheduling for 5 but 6 Int

// 11. Test fungsi hitungIPK secara spesifik
run { some m: Mahasiswa | hitungIPK[m] > 0 } for 4 but 5 Int

// 12. Test skenario dengan berbagai nilai IPK
run { 
    some m1, m2: Mahasiswa | 
        hitungIPK[m1] > hitungIPK[m2] and 
        hitungIPK[m1] > 300 
} for 4 but 5 Int

// 13. Comprehensive test dengan banyak constraints
run {
    #Mahasiswa >= 3
    #MataKuliah >= 4
    #Dosen >= 2
    some m: Mahasiswa | #m.mengambil >= 3
    some mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} > 1
} for 5 but 6 Int