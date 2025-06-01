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
            all m: Mahasiswa | m.nilai.univ in m.mengambil        }        // Fungsi untuk menghitung IPK - FIXED
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

//START - Assertion
// Assertion tambahan untuk memvalidasi model
assert IPKCalculationValid {
    // IPK yang dihitung harus dalam rentang yang wajar (0-400 untuk skala 4.00)
    all m: Mahasiswa | hitungIPK[m] >= 0 and hitungIPK[m] <= 400
}

assert PrerequisitesEnforced {
    // Jika mahasiswa mengambil mata kuliah dan registrasi valid, semua prasyaratnya harus dipenuhi
    all m: Mahasiswa | registrasiValid[m] implies 
        all mk: m.mengambil, prereq: mk.prasyarat | prereq in m.mengambil
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
//END - Assertion

//START - Predicates
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
//END - Assertion



//START - COMMANDS RUN
run { some Mahasiswa } for 5 but 6 Int //apakah bisa membuat mahasiswa
run { some MataKuliah } for 5 but 6 Int // Memperbesar scope untuk memungkinkan instance ditemukan
run { some m: Mahasiswa | some m.mengambil } for 5 but 6 Int // Memastikan mahasiswa mengambil setidaknya satu mata kuliah

run { some m: Mahasiswa | registrasiValid[m] } for 6 but 6 Int //melihat instance registrasi yang valid - scope diperbesar
run studentWithGrades for 4 but 5 Int //scenario dengan mahasiswa yang memiliki nilai
run fullCapacityCourse for 4 but 5 Int //scenario dengan mata kuliah penuh
run complexScheduling for 5 but 6 Int //scenario penjadwalan kompleks
run { 
    some m: Mahasiswa | 
        some mk: m.mengambil | some m.nilai[mk] and m.ipk > 0 
} for 6 but 7 Int // Test fungsi hitungIPK dengan target yang lebih realistis
run {
    #Mahasiswa >= 3
    #MataKuliah >= 4
    #Dosen >= 2
    some m: Mahasiswa | #m.mengambil >= 3
    some mk: MataKuliah | #{m: Mahasiswa | mk in m.mengambil} > 1
} for 5 but 6 Int //Comprehensive test dengan banyak constraints
// END - COMMANDS RUN



// START - COMMANDS CHECK
check IPKCalculationValid for 5 but 6 Int //Check IPK calculation validity
check PrerequisitesEnforced for 5 but 6 Int //Check prerequisites enforcement dengan scope lebih besar
check NoRoomConflicts for 4 but 5 Int  //Check room conflicts
check WaitlistConsistency for 4 but 5 Int //Check waitlist consistency  
check GradeConsistency for 4 but 5 Int //Check grade consistency
check InstructorWorkloadValid for 4 but 5 Int //Check instructor workload
// END - COMMANDS CHECK