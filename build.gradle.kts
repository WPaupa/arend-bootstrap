// Builds the Arend language extension for this library (the `do` meta, see
// meta/src/main/java/monad). The compiled classes are deployed into `ext`, which arend.yaml
// declares as `extensionsDir`. The extension API is provided at runtime by Arend, so it is a
// compile-only dependency taken from the bundled Arend.jar.
//
// Run `./gradlew deployExtension` (or just `./gradlew build`) after editing the Java sources,
// then typecheck the library with `java -jar Arend.jar -ai`.

plugins {
    java
}

repositories {
    mavenCentral()
}

dependencies {
    compileOnly(files("Arend.jar"))
}

sourceSets {
    main {
        java.setSrcDirs(listOf("meta/src/main/java"))
        resources.setSrcDirs(emptyList<String>())
    }
}

java {
    sourceCompatibility = JavaVersion.VERSION_21
    targetCompatibility = JavaVersion.VERSION_21
}

tasks.compileJava {
    options.encoding = "UTF-8"
}

// Mirror the compiled classes into the extensionsDir declared in arend.yaml.
val deployExtension by tasks.registering(Sync::class) {
    group = "build"
    description = "Compiles the extension and copies it into ext (the Arend extensionsDir)."
    dependsOn(tasks.classes)
    from(layout.buildDirectory.dir("classes/java/main"))
    into(layout.projectDirectory.dir("ext"))
}

tasks.named("assemble") {
    dependsOn(deployExtension)
}
